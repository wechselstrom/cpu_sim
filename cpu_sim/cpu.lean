import Mathlib.Logic.Function.Iterate

inductive Instr
| Noop : Instr          -- no operation
| Jump : Nat → Instr      -- jump to an instruction at a specific index
| JumpIfZero : Nat → Instr -- jump to a specific instruction if the accumulator is 0
| Dec : Instr           -- decrement the accumulator
| Halt : Instr          -- stop execution
| Add : Nat → Instr

inductive CpuException
| UnkownException : CpuException
| SegmentationFault : CpuException

structure CpuState :=
(ip : Nat) -- instruction pointer
(acc : Nat) -- accumulator

inductive TerminationState
| Running : TerminationState
| Exception : CpuException → TerminationState
| Halted : TerminationState

structure ExecutionState :=
(cpu_state : CpuState)
(termination_state : TerminationState)


def exec_instr (instr : Instr) (exec_st : ExecutionState) : ExecutionState :=
  let ip : Nat := exec_st.cpu_state.ip
  let acc : Nat := exec_st.cpu_state.acc
  let cpu_st : CpuState := exec_st.cpu_state
  match instr with
  | Instr.Noop =>  {exec_st with cpu_state := {cpu_st with ip := ip+1}}
  | Instr.Jump n => {exec_st with cpu_state := {cpu_st with ip := n}}
  | Instr.JumpIfZero n => {exec_st with cpu_state := {cpu_st with ip := if acc = 0 then n else ip + 1}}
  | Instr.Dec =>{exec_st with cpu_state := {cpu_st with ip := ip+1, acc := acc -1}}
  | Instr.Add n =>{exec_st with cpu_state := {cpu_st with ip := ip+1, acc := acc + n}}
  | Instr.Halt => {exec_st with termination_state := TerminationState.Halted}

def tiny_prog : Array Instr := #[Instr.Dec, Instr.JumpIfZero 3, Instr.Jump 0, Instr.Halt]

def step_prog (prog : Array Instr) (s : ExecutionState) : ExecutionState :=
  match prog[s.cpu_state.ip]? with
   | some instr => (exec_instr instr s)
   | none => {s with termination_state := TerminationState.Exception CpuException.SegmentationFault}


def run_prog_n_steps  (prog : Array Instr) (s : ExecutionState) (n : Nat) : ExecutionState :=
  (Nat.iterate (step_prog prog) n s)

theorem run_prog_repeated_application_is_additive : ∀ (a:Nat), ∀ (b:Nat),∀ (p:Array Instr), ∀ (e:ExecutionState),
 run_prog_n_steps  p e (a + b) = run_prog_n_steps p (run_prog_n_steps p e b) a := by
 simp [Function.iterate_add, run_prog_n_steps]

theorem tiny_prog_terminates_with_fixed_accumulator : ∃ (n : Nat), (run_prog_n_steps tiny_prog ⟨⟨0, 3⟩, TerminationState.Running⟩ n).termination_state = TerminationState.Halted := 
  ⟨ 9, rfl⟩

theorem running_tiny_prog_decreases_acc :
  ∀ (acc : Nat), (h₀: 0 < acc) → ∀ (n : Nat),
    run_prog_n_steps  tiny_prog ⟨⟨0, acc+1⟩, TerminationState.Running⟩ (n + 3)=
    run_prog_n_steps tiny_prog ⟨⟨0, acc⟩, TerminationState.Running⟩ n := by
      have h₁ : ∀ (acc : Nat), acc > 0 → ∀ (n : Nat),
       run_prog_n_steps tiny_prog ⟨⟨0, acc+1⟩, TerminationState.Running⟩ (n+3) =
       run_prog_n_steps tiny_prog ⟨⟨1, acc  ⟩, TerminationState.Running⟩ (n+2) := by
        intros acc h₀ n
        simp [run_prog_n_steps, step_prog, exec_instr, tiny_prog, h₀]
      
      have h₂  : ∀ (acc : Nat), acc > 0 → ∀ (n : Nat),
       run_prog_n_steps tiny_prog ⟨⟨1, acc⟩, TerminationState.Running⟩ (n+2) =
       run_prog_n_steps tiny_prog ⟨⟨2, acc⟩, TerminationState.Running⟩ (n+1) := by
        intros acc h₀ n

        simp [run_prog_n_steps, step_prog, exec_instr, tiny_prog, h₀, if_neg, Nat.ne_of_gt]



      have h₃  : ∀ (acc : Nat), acc > 0 → ∀ (n : Nat),
       run_prog_n_steps tiny_prog ⟨⟨2, acc⟩, TerminationState.Running⟩ (n+1) =
       run_prog_n_steps tiny_prog ⟨⟨0, acc⟩, TerminationState.Running⟩  n := by
        intros acc h₀ n
        simp [run_prog_n_steps, step_prog, exec_instr, tiny_prog, h₀]
      
      intros acc h₀ n

      have step1 := h₁ acc h₀ n
      rw [step1]

      have step2 := h₂ acc h₀ n
      rw [step2]

      have step3 := h₃ acc h₀ n
      rw [step3]


theorem tiny_prog_reduces_acc_to_zero :
  ∀ (init_acc : Nat), ∃ (n : Nat),
  (run_prog_n_steps tiny_prog ⟨⟨0, init_acc⟩, TerminationState.Running⟩) n = ⟨ ⟨ 1, 0⟩, TerminationState.Running⟩  := by
  intro init_acc
  match init_acc with
  | 0 =>
    exists 1
  | 1 =>
    exists 1
  | d +2 =>
    obtain ⟨n, ih⟩ := tiny_prog_reduces_acc_to_zero (d+1)
    -- After 3 steps, the accumulator decreases by 1.
    exists (n + 3)

theorem tiny_prog_terminates :
  ∀ (init_acc : Nat), ∃ (n : Nat),
  (run_prog_n_steps tiny_prog ⟨⟨0, init_acc⟩, TerminationState.Running⟩ n ).termination_state = TerminationState.Halted := by
  intro init_acc

  -- Use the theorem tiny_prog_reduces_acc_to_zero to find n
  obtain ⟨n, h₀⟩ := tiny_prog_reduces_acc_to_zero init_acc
  have h₁:(run_prog_n_steps tiny_prog ⟨⟨1, 0⟩, TerminationState.Running⟩ 2 =  ⟨⟨3, 0⟩, TerminationState.Halted⟩):= by
    simp [run_prog_n_steps, step_prog, tiny_prog, exec_instr]
  have h₂ : run_prog_n_steps tiny_prog ⟨⟨0, init_acc⟩, TerminationState.Running⟩ (2 + n) =  ⟨⟨3, 0⟩, TerminationState.Halted⟩ := by
    rw [run_prog_repeated_application_is_additive 2 (n:Nat)]
    rw [← h₁] 
    rw [← h₀]
    
  have h₃ : ∀ (cpu_state:CpuState),
   ({cpu_state:=cpu_state, termination_state:=TerminationState.Halted} : ExecutionState).termination_state = TerminationState.Halted := by

    simp [ExecutionState.termination_state]
  rw [← h₃]
  
  -- Finally, we can conclude the existence of n
  exists 2+n

  rw  [h₂] 

#check tiny_prog_terminates

-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:17:59.602319+00:00
-- url     : https://prove2.me/submissions/eab02b9b-042e-4aae-867d-603c07439f3d

import Mathlib
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_visits_exists

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native full-key computation for the resumable attained-signature scan

One invocation preserves the assignment and all raw integer constraint rows.
Its local polynomial-time bound controls every scratch stack at every source
prefix. The generator retains candidate and predecessor cursors separately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

theorem clear_eval (i : Fin 24) (a : Data) :
    Eval (clear i) (2 * (a.stacks i).length + 3) a
      ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks i a.stacks⟩ :=
  .call _ (ListRegisterProgram.clear_run i 0 1 a.regs a.stacks)

theorem copy_eval (i j : Fin 24) (a : Data)
    (hij : i ≠ j) (hi : i ≠ 21) (hj : (21 : Fin 24) ≠ j)
    (ht : a.stacks 21 = []) :
    Eval (copy i j) (7 * (a.stacks i).length + 5) a
      ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks i j a.stacks⟩ :=
  .call _ (ListRegisterProgram.copy_run i j 21 0 1 hij hi hj (by decide)
    a.regs a.stacks ht)

theorem storeFresh_eval (b : Bool) (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (bits key : List Bool) :
    ∃ out, Eval (storeFresh b) 7
      (workState regs W rows candidate saved predecessor fuel fresh bits key)
      (workState out W rows candidate saved predecessor fuel b bits key) := by
  let a := workState regs W rows candidate saved predecessor fuel fresh bits key
  let c : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 22 a.stacks⟩
  let d := (StructuredProgram.Atom.set (0 : Fin 16) b).eval c
  let e := (StructuredProgram.Atom.push (22 : Fin 24) (0 : Fin 16)).eval d
  have hc : Eval (clear 22) 5 a c := clear_eval 22 a
  have he : Eval (.base (.seq (.atom (.set 0 b)) (.atom (.push 22 0)))) 2 c e :=
    .base ((StructuredProgram.Eval.atom _ c).seq (StructuredProgram.Eval.atom _ d))
  have hf : e = workState e.regs W rows candidate saved predecessor fuel b bits key := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i <;> simp [d, c, a, workState, StackRoutines.clearStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  refine ⟨e.regs, ?_⟩
  have ht := hc.seq he
  rw [hf] at ht
  exact ht

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureRescan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual bounded-word predecessor rescan and its uniform source-prefix storage. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

theorem for_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) :
    ∃ n ≤ candidate.val *
        (bodyBound W (naturalKey W rows h candidate) rows h B + 16 * h + 16) + 8 * h + 8,
      ∃ out, Eval (CounterForPrograms.forCmd countdownPorts body) n
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
          (ExecCNFTupleEnumeration.fixedBits h candidate) true [] [])
        (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h candidate)
          (List.replicate h false)
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) := by
  let a := workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
    (ExecCNFTupleEnumeration.fixedBits h candidate) true [] []
  let t := CounterForPrograms.testResult countdownPorts a
  have ht : t = workState t.regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
      (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
      (ExecCNFTupleEnumeration.fixedBits h candidate) true [] [] := by
    apply congrArg (StructuredProgram.State.mk t.regs)
    exact CounterForPrograms.testResult_stacks countdownPorts a rfl
  have hf : t.regs 15 = !(CounterPrograms.isZero (ExecCNFTupleEnumeration.fixedBits h candidate)) :=
    CounterForPrograms.testResult_flag countdownPorts a
  obtain ⟨costs, ns, out, hv, hc⟩ := visits_exists W rows h B hlen hwidth candidate candidate.val
    0 (ExecCNFTupleEnumeration.fixedBits h candidate) t.regs (by omega) (by simp)
    (ExecCNFTupleEnumeration.fixedBits_value h candidate candidate.isLt) hf
  simp only [AttainedSignatures.duplicateScan, Bool.not_false] at hv
  rw [← ht] at hv
  have htest := CounterForPrograms.test_eval countdownPorts a (by rfl)
  have hrun := htest.seq hv.eval
  obtain ⟨hcount, _, _, htime⟩ := hv.bounds
  have hlen' : (t.stacks countdownPorts.counter).length = h := by
    rw [ht]
    simp [workState, countdownPorts]
  have hval : CounterPrograms.value (t.stacks countdownPorts.counter) = candidate.val := by
    rw [ht]
    exact ExecCNFTupleEnumeration.fixedBits_value h candidate candidate.isLt
  rw [hval] at hcount
  rw [hlen', hcount] at htime
  refine ⟨_, ?_, out, hrun⟩
  change 8 * (ExecCNFTupleEnumeration.fixedBits h candidate).length + 7 + ns ≤ _
  rw [ExecCNFTupleEnumeration.fixedBits_length]
  nlinarith

theorem setup_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor : List Bool) (fresh : Bool) :
    ∃ out, Eval setup (7 * candidate.length + 12)
      (workState regs W rows candidate saved predecessor [] fresh [] [])
      (workState out W rows candidate saved predecessor candidate true [] []) := by
  let a := workState regs W rows candidate saved predecessor [] fresh [] []
  let r₁ := readRegs regs 0 1 none
  have hcopy : Eval (copy 16 19) (7 * candidate.length + 5) a
      (workState r₁ W rows candidate saved predecessor candidate fresh [] []) := by
    have ht := copy_eval 16 19 a (by decide) (by decide) (by decide) rfl
    have he : (⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 16 19 a.stacks⟩ : Data) =
        workState r₁ W rows candidate saved predecessor candidate fresh [] [] := by
      apply congrArg (StructuredProgram.State.mk r₁)
      funext i
      fin_cases i <;> simp [a, workState, StackRoutines.copyStacks]
    rw [he] at ht
    exact ht
  obtain ⟨r₂, hf⟩ := storeFresh_eval true r₁ W rows candidate saved predecessor candidate fresh [] []
  exact ⟨r₂, by simpa only [setup] using hcopy.seq hf⟩

theorem cleanup_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved : List Bool) (h : ℕ) (answer : Bool) :
    ∃ out, Eval cleanup (2 * candidate.length + 3 * h + 6)
      (workState regs W rows candidate saved candidate (List.replicate h false) answer [] [])
      (workState out W rows candidate saved (List.replicate h false) [] answer [] []) := by
  let r₁ := readRegs regs 0 1 none
  have hclear : Eval (clear 18) (2 * candidate.length + 3)
      (workState regs W rows candidate saved candidate (List.replicate h false) answer [] [])
      (workState r₁ W rows candidate saved [] (List.replicate h false) answer [] []) := by
    have ht := clear_eval 18
      (workState regs W rows candidate saved candidate (List.replicate h false) answer [] [])
    have he : StackRoutines.clearStacks 18
        (workState regs W rows candidate saved candidate (List.replicate h false) answer [] []).stacks =
        (workState r₁ W rows candidate saved [] (List.replicate h false) answer [] []).stacks := by
      funext i
      fin_cases i <;> simp [workState, StackRoutines.clearStacks]
    rw [he] at ht
    exact ht
  let b := workState r₁ W rows candidate saved [] (List.replicate h false) answer [] []
  let r₂ := readRegs r₁ 0 1 none
  have htransfer : Eval (.call (StackRoutines.transferProgram 19 18 0 1)) (3 * h + 3) b
      (workState r₂ W rows candidate saved (List.replicate h false) [] answer [] []) := by
    have ht : Eval (.call (StackRoutines.transferProgram 19 18 0 1))
        (3 * (b.stacks 19).length + 3) b
        ⟨readRegs b.regs 0 1 none, StackRoutines.transferStacks 19 18 b.stacks⟩ :=
      .call _ (ListRegisterProgram.transfer_run (19 : Fin 24) 18
        (0 : Fin 16) 1 (by decide) (by decide) b.regs b.stacks)
    have he : StackRoutines.transferStacks 19 18 b.stacks =
        (workState r₂ W rows candidate saved (List.replicate h false) [] answer [] []).stacks := by
      funext i
      fin_cases i <;> simp [b, workState, StackRoutines.transferStacks]
    rw [he] at ht
    have htarget :
        (⟨readRegs b.regs 0 1 none,
          (workState r₂ W rows candidate saved (List.replicate h false) [] answer [] []).stacks⟩ :
            Data) =
          workState r₂ W rows candidate saved (List.replicate h false) [] answer [] [] := by
      apply congrArg₂ StructuredProgram.State.mk <;> rfl
    rw [htarget] at ht
    change Eval (.call (StackRoutines.transferProgram 19 18 0 1))
      (3 * (List.replicate h false).length + 3) b _ at ht
    simpa only [List.length_replicate] using ht
  refine ⟨r₂, ?_⟩
  convert hclear.seq htransfer using 1
  · rfl
  · omega

theorem command_eval_oai (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool) :
    ∃ n ≤ candidate.val *
        (bodyBound W (naturalKey W rows h candidate) rows h B + 16 * h + 16) + 20 * h + 26,
      ∃ out, Eval command n
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
          [] fresh [] [])
        (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (List.replicate h false) []
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) := by
  obtain ⟨r₁, hs⟩ := setup_eval regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0) fresh
  obtain ⟨nf, hnf, rf, hf⟩ := for_eval r₁ W rows h B hlen hwidth candidate
  obtain ⟨r₂, hc⟩ := cleanup_eval rf W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) h
    (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate))
  refine ⟨_, ?_, r₂, hs.seq (hf.seq hc)⟩
  simp only [ExecCNFTupleEnumeration.fixedBits_length]
  omega


end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.command_eval_oai

-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.command_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:31:59.143993+00:00
-- url     : https://prove2.me/submissions/efff1e1f-9c45-413d-8825-eac6cc1524a6

import Mathlib
import Definitions.Def_OAIQ081S115
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Cofactor_scan_state_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete tape operations and traversal assertions for the outer CRT.
All operations in this module are fixed finite programs. Arithmetic is supplied
by the separately defined concrete CRT service commands. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem copy_run (d : Data) (src dst : Fin 320)
    (hsd : src ≠ dst) (hs : src ≠ 318) (hd : (318 : Fin 320) ≠ dst)
    (ht : d.stacks 318 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d
      (afterCopy d src dst 0 1) :=
  SubexpScanPrimitives.copy_eval d src dst 318 0 1 hsd hs hd (by decide) ht

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual initialization for the outer CRT tape controller. Widths and the
binary dimension are computed by fixed programs from the retained runtime
inputs. In particular, neither a binary exponent nor a jet-width word is
provided for free. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem move_run (d : Data) (src dst : Fin 320)
    (hs : src ≠ 319) (hd : dst ≠ 319) (hsd : src ≠ dst)
    (ht : d.stacks 319 = []) (he : d.stacks dst = []) :
    Eval (move src dst) (6 * (d.stacks src).length + 6) d (moved d src dst) := by
  have h1 := transfer_eval d src 319 0 1 hs (by decide)
  let mid := afterTransfer d src 319 0 1
  have h2 := transfer_eval mid 319 dst 0 1 hd.symm (by decide)
  have hlen : (mid.stacks 319).length = (d.stacks src).length := by
    simp [mid, afterTransfer, StackRoutines.transferStacks, ht]
  have hfinal : afterTransfer mid 319 dst 0 1 = moved d src dst := by
    apply state_ext
    · simp [mid, afterTransfer, StackRoutines.readRegs_reset]
    · funext i
      by_cases hi : i = dst
      · subst i
        simp [mid, afterTransfer, StackRoutines.transferStacks, hd, hsd.symm, ht, he]
      · by_cases hj : i = src
        · subst i
          simp [mid, afterTransfer, StackRoutines.transferStacks, hs, hsd ]
        · by_cases hk : i = 319
          · subst i
            simp [mid, afterTransfer, StackRoutines.transferStacks, hi, hs.symm, ht]
          · simp [mid, afterTransfer, StackRoutines.transferStacks, hi, hj, hk]
  rw [hfinal] at h2
  have h := h1.seq h2
  simpa only [move, transfer, hlen,
    show 3 * (d.stacks src).length + 3 + (3 * (d.stacks src).length + 3) =
      6 * (d.stacks src).length + 6 by omega] using h

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Final cleanup and complete tape-loop costs for scalar reconstruction.
The arithmetic-middle premise below is an actual execution of a fixed command;
its concrete implementation is assembled separately from the CRT services. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open scoped BigOperators

theorem flatMap_length_of_width {I : Type*} (encode : I → List Bool) (W : ℕ)
    (hw : ∀ x, (encode x).length = W) (xs : List I) :
    (xs.flatMap encode).length = xs.length * W := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, hw, Nat.add_mul, Nat.add_comm]

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed invocation of the fixed lower-256 arithmetic controllers. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram

theorem lowerCall_run (code : Cmd 16 256) (input output : Fin 256)
    (d : Data) (after : Fin 256 → List Bool) (K : ℕ)
    (h : SubexpConvolutionControl.ExecutesIn code K (d.stacks ∘ localPorts) after) :
    ∃ n ≤ K + 1, ∃ rf, Eval (lowerCall code input output) n d
      ⟨rf, Function.extend localPorts after d.stacks⟩ := by
  obtain ⟨n, rf, hn, ht⟩ := h d.regs
  have he := eval_liftCommand_from_state code input output id localPorts d
    Function.injective_id localPorts.injective ht
  exact ⟨n + 1, by omega, Function.extend id rf d.regs, he⟩

theorem lower_extend_project (d : Data) :
    Function.extend localPorts (d.stacks ∘ localPorts) d.stacks = d.stacks :=
  congrArg StructuredProgram.State.stacks
    (embedState_project id localPorts d Function.injective_id localPorts.injective)

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

theorem command_run_oai {C : Type*} (encode : C → List Bool)
    (multiply : Cmd 16 256) (mulOp : C → C → C) (K W J : ℕ)
    (d : Data) (remaining processed : List C) (unit minusOne : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp K)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (hr : d.stacks 257 = remaining.flatMap encode)
    (hp : d.stacks 258 = processed.flatMap encode)
    (hu : d.stacks 207 = encode unit) (hn : d.stacks 211 = encode minusOne)
    (hJ : d.stacks 243 = List.replicate J true) (hwidth : (d.stacks 104).length = W)
    (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
    ∃ n ≤ budget (remaining.length + processed.length) K W J, ∃ rf,
      Eval (command multiply) n d
        ⟨rf, Function.update d.stacks 262
          (encode ((remaining ++ processed).foldl (Cofactor.includeValue mulOp minusOne J) unit))⟩ := by
  let value := (remaining ++ processed).foldl (Cofactor.includeValue mulOp minusOne J) unit
  let d1 := afterCopy d 258 215 0 1
  let d2 := afterCopy d1 257 215 0 1
  let d3 := afterCopy d2 207 240 0 1
  let s := d3.stacks ∘ localPorts
  have h1 := copy_run d 258 215 (by decide) (by decide) (by decide) (hc 318 (by simp [cleanPorts]))
  have h2 := copy_run d1 257 215 (by decide) (by decide) (by decide)
    (by simpa [d1, afterCopy, StackRoutines.copyStacks] using hc 318 (by simp [cleanPorts]))
  have h3 := copy_run d2 207 240 (by decide) (by decide) (by decide)
    (by simpa [d2, d1, afterCopy, StackRoutines.copyStacks] using hc 318 (by simp [cleanPorts]))
  have hf : LowFrame (d.stacks ∘ localPorts) s := by
    intro i hi
    have h215 : localPorts i ≠ (215 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 215 at hv; omega
    have h240 : localPorts i ≠ (240 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 240 at hv; omega
    simp [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, Function.comp_def, h215, h240]
  have hscan := Cofactor.scan_state_run (d.stacks ∘ localPorts) encode multiply mulOp minusOne K W J
    hm hw hW s hf (remaining ++ processed) unit
    (by simpa [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts] using hn)
    (by simpa [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts] using hJ)
    (by simpa [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts] using hwidth)
    (by simp [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts,
      hr, hp, hc 215 (by simp [cleanPorts]), List.flatMap_append])
    (by simp [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts,
      hu, hc 240 (by simp [cleanPorts])])
    (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts] using hc _ (by simp [cleanPorts]))
  obtain ⟨nl, hnl, rl, hl⟩ := lowerCall_run (Cofactor.scan multiply) 215 240 d3 _ _ hscan
  have he : Function.extend localPorts (Function.update (Function.update s 215 []) 240 (encode value))
      d3.stacks = Function.update (Function.update d3.stacks 215 []) 240 (encode value) := by
    rw [ProgramLinking.extend_update localPorts.injective, ProgramLinking.extend_update localPorts.injective,
      lower_extend_project]
    rfl
  change Eval _ nl d3 ⟨rl, Function.extend localPorts
    (Function.update (Function.update s 215 []) 240 (encode value)) d3.stacks⟩ at hl
  rw [he] at hl
  let d4 : Data := ⟨rl, Function.update (Function.update d3.stacks 215 []) 240 (encode value)⟩
  have h4 := move_run d4 240 262 (by decide) (by decide) (by decide)
    (by simpa [d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hc 319 (by simp [cleanPorts]))
    (by simpa [d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hc 262 (by simp [cleanPorts]))
  have hfinal : (moved d4 240 262).stacks = Function.update d.stacks 262 (encode value) := by
    funext i
    by_cases h215 : i = 215 <;> by_cases h240 : i = 240 <;>
      simp [ d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, Function.update_apply,
        h215, h240, hc 215 (by simp [cleanPorts]), hc 240 (by simp [cleanPorts])]
  have heq : moved d4 240 262 = (⟨(moved d4 240 262).regs,
      Function.update d.stacks 262 (encode value)⟩ : Data) := state_ext rfl hfinal
  have hrun := h1.seq (h2.seq (h3.seq (hl.seq h4)))
  rw [heq] at hrun
  refine ⟨_, ?_, _, hrun⟩
  have hrl := flatMap_length_of_width encode W hw remaining
  have hpl := flatMap_length_of_width encode W hw processed
  simp only [List.length_append] at hnl
  simp [d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, hp, hr, hu, hw, hrl, hpl, budget]
  nlinarith

end SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.command_run_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.command_run_oai.{u_1}

-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.negative_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:37:13.526153+00:00
-- url     : https://prove2.me/submissions/ce00dcc0-7835-48b5-abb0-1ed9581ce26b

import Mathlib
import Definitions.Def_OAIQ081S115
import Definitions.Def_OAIQ081S144

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

theorem clear_run (d : Data) (src : Fin 320) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d
      (SubexpSetupStorage.clearState src d) :=
  SubexpSetupStorage.clear_eval src d

theorem clearMany_run (d : Data) (ports : List (Fin 320)) :
    Eval (clearMany ports) (SubexpSetupStorage.clearManyCost ports d) d
      (SubexpSetupStorage.clearManyState ports d) := by
  have he : clearMany ports = SubexpSetupStorage.clearMany ports := by
    induction ports with
    | nil => rfl
    | cons p ps ih =>
      change Cmd.seq (clear p) (clearMany ps) =
        Cmd.seq (SubexpSetupStorage.clearCmd p) (SubexpSetupStorage.clearMany ps)
      rw [ih]
      rfl
  rw [he]
  exact SubexpSetupStorage.clearMany_eval ports d

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed outer calls to the native scalar ring arithmetic. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

theorem binary_run {C : Type*} (encode : C → List Bool) (code : Cmd 16 256)
    (op : C → C → C) (K W : ℕ) (d : Data) (src right dst : Fin 320)
    (hs : safe src) (hr : safe right) (hd : safe dst)
    (hcode : ServiceSpec (d.stacks ∘ localPorts) encode code op K)
    (hw : ∀ a, (encode a).length = W) (a b : C)
    (ha : d.stacks src = encode a) (hb : d.stacks right = encode b)
    (hdw : (d.stacks dst).length ≤ W)
    (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
    ∃ n ≤ K + 26 * W + 26, ∃ rf,
      Eval (binary code src right dst) n d ⟨rf, Function.update d.stacks dst (encode (op a b))⟩ := by
  rcases hs with ⟨hs0, hs1, hs4, hs8, hs9⟩
  rcases hr with ⟨hr0, hr1, hr4, hr8, hr9⟩
  rcases hd with ⟨hd0, hd1, hd4, hd8, hd9⟩
  let d1 := afterCopy d src 240 0 1
  let d2 := afterCopy d1 right 241 0 1
  let s := d2.stacks ∘ localPorts
  have h1 := copy_run d src 240 hs0 hs8 (by decide) (hc 318 (by simp [cleanPorts]))
  have h2 := copy_run d1 right 241 hr1 hr8 (by decide)
    (by simpa [d1, afterCopy, StackRoutines.copyStacks] using hc 318 (by simp [cleanPorts]))
  have hf : LowFrame (d.stacks ∘ localPorts) s := by
    intro i hi
    have h0 : localPorts i ≠ (240 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 240 at hv; omega
    have h1 : localPorts i ≠ (241 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 241 at hv; omega
    simp [s, d2, d1, afterCopy, StackRoutines.copyStacks, Function.comp_def, h0, h1]
  have hcall := CRTLocalProgram.serviceSpec_frame hcode hf s a b (CRTLocalProgram.lowFrame_refl s)
    (by simp [s, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts, ha,
      hc 240 (by simp [cleanPorts])])
    (by simp [s, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts, hb, hr0,
      hc 241 (by simp [cleanPorts])])
    (by simpa [s, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts]
      using hc 244 (by simp [cleanPorts]))
    (by simpa [s, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts]
      using hc 245 (by simp [cleanPorts]))
  obtain ⟨nl, hnl, rl, hl⟩ := lowerCall_run code 240 244 d2 _ K hcall
  have he : Function.extend localPorts (Function.update s 244 (encode (op a b))) d2.stacks =
      Function.update d2.stacks 244 (encode (op a b)) := by
    rw [ProgramLinking.extend_update localPorts.injective, lower_extend_project]
    rfl
  rw [he] at hl
  let d3 : Data := ⟨rl, Function.update d2.stacks 244 (encode (op a b))⟩
  have h3 := clear_run d3 dst
  let d4 := SubexpSetupStorage.clearState dst d3
  have h4 := move_run d4 244 dst (by decide) hd9 (Ne.symm hd4)
    (by simpa [d4, SubexpSetupStorage.clearState, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      Ne.symm hd9] using hc 319 (by simp [cleanPorts]))
    (by simp [d4, SubexpSetupStorage.clearState])
  let d5 := moved d4 244 dst
  have h5 := clearMany_run d5 [240,241]
  have hfinal : (SubexpSetupStorage.clearManyState [240,241] d5).stacks =
      Function.update d.stacks dst (encode (op a b)) := by
    funext i
    by_cases h0 : i = 240 <;> by_cases h1 : i = 241 <;> by_cases h4 : i = 244 <;>
      by_cases hd : i = dst <;>
      simp [SubexpSetupStorage.clearManyState, SubexpSetupStorage.clearState,
        d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
        Function.update_apply, h0, h1, h4, hd, hd0, hd1,
        Ne.symm hd0, Ne.symm hd1, Ne.symm hd4,
        hc 240 (by simp [cleanPorts]), hc 241 (by simp [cleanPorts]), hc 244 (by simp [cleanPorts])]
  have hrun := h1.seq (h2.seq (hl.seq (h3.seq (h4.seq h5))))
  have heq : SubexpSetupStorage.clearManyState [240,241] d5 =
      (⟨(SubexpSetupStorage.clearManyState [240,241] d5).regs,
        Function.update d.stacks dst (encode (op a b))⟩ : Data) := state_ext rfl hfinal
  rw [heq] at hrun
  refine ⟨_, ?_, _, hrun⟩
  simp [d5, d4, SubexpSetupStorage.clearState, d3, d2, d1, afterCopy, StackRoutines.copyStacks, SubexpSetupStorage.clearManyCost, ha, hb, hw, hr0, hd0, hd1, hd4,
    Ne.symm hd0, Ne.symm hd1, Ne.symm hd4,
    hc 240 (by simp [cleanPorts]), hc 241 (by simp [cleanPorts])]
  omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramScalarSteps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec)

theorem negative_run_oai {C : Type*} (encode : C → List Bool) (multiply : Cmd 16 256)
    (mulOp : C → C → C) (K W : ℕ) (d : Data) (node minusOne : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp K)
    (hw : ∀ a, (encode a).length = W)
    (hn : d.stacks 259 = encode node) (hminus : d.stacks 211 = encode minusOne)
    (h263 : d.stacks 263 = []) (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
    ∃ n ≤ K + 26 * W + 26, ∃ rf, Eval (negative multiply) n d
      ⟨rf, Function.update d.stacks 263 (encode (mulOp node minusOne))⟩ := by
  exact binary_run encode multiply mulOp K W d 259 211 263
    (by unfold safe; decide) (by unfold safe; decide) (by unfold safe; decide) hm hw node minusOne hn hminus
    (by simp [h263]) hc

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.negative_run_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.negative_run_oai.{u_1}

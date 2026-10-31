-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.command_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:33:45.082095+00:00
-- url     : https://prove2.me/submissions/f6fa3f58-3259-460f-86bf-46284cf07be0

import Mathlib
import Definitions.Def_OAIQ081S115
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HornerProgram_command_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact native evaluation of a dynamically sized dense polynomial. Input
coefficients are in increasing degree order. Every other persistent stack is
preserved; the input stream and runtime counter are consumed. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec serviceSpec_frame lowFrame_refl lowFrame_update)

theorem encodePolynomial_length {C : Type*} (encode : C → List Bool) (W : ℕ)
    (hw : ∀ a, (encode a).length = W) (P : List C) :
    (encodePolynomial encode P).length = P.length * W := by
  induction P with
  | nil => simp [encodePolynomial]
  | cons c P ih => simp [encodePolynomial, hw, Nat.add_mul, Nat.add_comm]

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramHorner
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical staging of local CRT correction evaluation. The dense correction
is consumed from 244; its value at the retained point 263 is returned on 264. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

theorem command_run_oai {C : Type*} (encode : C → List Bool)
    (multiply add : Cmd 16 256) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (d : Data) (P : List C) (point zero : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp Km)
    (ha : ServiceSpec (d.stacks ∘ localPorts) encode add addOp Ka)
    (hw : ∀ a, (encode a).length = W)
    (hP : d.stacks 244 = HornerProgram.encodePolynomial encode P)
    (hx : d.stacks 263 = encode point) (hz : d.stacks 104 = encode zero)
    (hJ : (d.stacks 243).length = P.length)
    (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
    ∃ n ≤ budget P.length W Km Ka, ∃ rf,
      Eval (command multiply add) n d
        ⟨rf, Function.update (Function.update d.stacks 244 [])
          264 (encode (HornerProgram.fold (HornerProgram.stepValue mulOp addOp point) P.reverse zero))⟩ := by
  let value := HornerProgram.fold (HornerProgram.stepValue mulOp addOp point) P.reverse zero
  let d1 := moved d 244 246
  let d2 := afterCopy d1 263 247 0 1
  let d3 := afterCopy d2 243 248 0 1
  let d4 := afterCopy d3 104 250 0 1
  let d5 := afterCopy d4 104 240 0 1
  have h1 := move_run d 244 246 (by decide) (by decide) (by decide)
    (hc 319 (by simp [cleanPorts])) (hc 246 (by simp [cleanPorts]))
  have h2 := copy_run d1 263 247 (by decide) (by decide) (by decide)
    (by simpa [d1, moved] using hc 318 (by simp [cleanPorts]))
  have h3 := copy_run d2 243 248 (by decide) (by decide) (by decide)
    (by simpa [d2, d1, afterCopy, StackRoutines.copyStacks, moved] using hc 318 (by simp [cleanPorts]))
  have h4 := copy_run d3 104 250 (by decide) (by decide) (by decide)
    (by simpa [d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved] using hc 318 (by simp [cleanPorts]))
  have h5 := copy_run d4 104 240 (by decide) (by decide) (by decide)
    (by simpa [d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved] using hc 318 (by simp [cleanPorts]))
  let s := d5.stacks ∘ localPorts
  have hf : LowFrame (d.stacks ∘ localPorts) s := by
    intro i hi
    have hn (q : Fin 320) (hq : 205 ≤ q.val) : localPorts i ≠ q := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = q.val at hv
      omega
    simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      Function.comp_def, hn 240 (by decide), hn 244 (by decide), hn 246 (by decide),
      hn 247 (by decide), hn 248 (by decide), hn 250 (by decide)]
  have hscalar := HornerProgram.command_run s encode multiply add mulOp addOp Km Ka W
    (CRTLocalProgram.serviceSpec_frame hm hf) (CRTLocalProgram.serviceSpec_frame ha hf) hw P point zero
    (by simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      localPorts, hP])
    (by simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      localPorts, hx, hc 247 (by simp [cleanPorts])])
    (by simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      localPorts, hz, hc 240 (by simp [cleanPorts])])
    (by simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      localPorts, hJ, hc 248 (by simp [cleanPorts])])
    (by simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      localPorts, hz, hw, hc 250 (by simp [cleanPorts])])
    (by simpa [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved,
      localPorts] using hc 120 (by simp [cleanPorts]))
    (by simpa [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved,
      localPorts] using hc 241 (by simp [cleanPorts]))
    (by simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts])
    (by simpa [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved,
      localPorts] using hc 245 (by simp [cleanPorts]))
    (by simpa [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved,
      localPorts] using hc 251 (by simp [cleanPorts]))
    (by simpa [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved,
      localPorts] using hc 252 (by simp [cleanPorts]))
  obtain ⟨nl, hnl, rl, hl⟩ := lowerCall_run (HornerProgram.command multiply add) 246 240 d5 _
    (HornerProgram.budget P.length W Km Ka) hscalar
  have hs : Function.extend localPorts
      (Function.update (Function.update (Function.update s 246 []) 240 (encode value)) 248 []) d5.stacks =
      Function.update (Function.update (Function.update d5.stacks 246 []) 240 (encode value)) 248 [] := by
    rw [ProgramLinking.extend_update localPorts.injective,
      ProgramLinking.extend_update localPorts.injective, ProgramLinking.extend_update localPorts.injective]
    rw [lower_extend_project]
    rfl
  change Eval _ nl d5 ⟨rl, Function.extend localPorts
    (Function.update (Function.update (Function.update s 246 []) 240 (encode value)) 248 []) d5.stacks⟩ at hl
  rw [hs] at hl
  let d6 : Data := ⟨rl, Function.update (Function.update (Function.update d5.stacks 246 [])
    240 (encode value)) 248 []⟩
  have h6 := move_run d6 240 264 (by decide) (by decide) (by decide)
    (by simpa [d6, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved]
      using hc 319 (by simp [cleanPorts]))
    (by simpa [d6, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved]
      using hc 264 (by simp [cleanPorts]))
  let d7 := moved d6 240 264
  have h7 := clearMany_run d7 [247,250]
  have hfinal : (SubexpSetupStorage.clearManyState [247,250] d7).stacks =
      Function.update (Function.update d.stacks 244 []) 264 (encode value) := by
    funext i
    by_cases h240 : i = 240 <;> by_cases h246 : i = 246 <;> by_cases h248 : i = 248 <;>
      by_cases h247 : i = 247 <;> by_cases h250 : i = 250 <;>
      simp [SubexpSetupStorage.clearManyState, SubexpSetupStorage.clearState,
        d7, d6, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
        Function.update_apply, h240, h246, h248, h247, h250,
        hc 240 (by simp [cleanPorts]), hc 246 (by simp [cleanPorts]),
        hc 248 (by simp [cleanPorts]), hc 247 (by simp [cleanPorts]), hc 250 (by simp [cleanPorts])]
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (hl.seq (h6.seq h7))))))
  have hstate : SubexpSetupStorage.clearManyState [247,250] d7 =
      (⟨(SubexpSetupStorage.clearManyState [247,250] d7).regs,
        Function.update (Function.update d.stacks 244 []) 264 (encode value)⟩ : Data) :=
    state_ext rfl hfinal
  rw [hstate] at hrun
  refine ⟨_, ?_, _, hrun⟩
  have hpLen := HornerProgram.encodePolynomial_length encode W hw P
  simp [d7, d6, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
    SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearState,
    hP, hx, hz, hw, hpLen, hJ, budget,
    hc 247 (by simp [cleanPorts]), hc 250 (by simp [cleanPorts])]
  nlinarith

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.command_run_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.command_run_oai.{u_1}

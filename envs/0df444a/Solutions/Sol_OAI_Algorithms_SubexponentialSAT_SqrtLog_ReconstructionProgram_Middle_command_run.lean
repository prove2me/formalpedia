-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:34:11.558586+00:00
-- url     : https://prove2.me/submissions/90d25b0e-99f9-4243-ae7b-00f478b2d51d

import Mathlib
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_CofactorOuter_command_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Horner_command_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Scalar_accumulate_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Scalar_negative_run

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramLocal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid cache setup and framing for the lower local Hermite-CRT routine. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Local

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

theorem command_run (localCode : Cmd 16 256) (d : Data) (output : List Bool) (K : ℕ)
    (h192 : d.stacks 192 = []) (h193 : d.stacks 193 = []) (h318 : d.stacks 318 = [])
    (hlocal : SubexpConvolutionControl.ExecutesIn localCode K
      ((prepared d).stacks ∘ localPorts)
      (Function.update ((prepared d).stacks ∘ localPorts) 244 output)) :
    ∃ n ≤ budget (d.stacks 277).length (d.stacks 243).length K, ∃ rf,
      Eval (command localCode) n d ⟨rf, Function.update d.stacks 244 output⟩ := by
  have h1 := copy_run d 277 192 (by decide) (by decide) (by decide) h318
  let d1 := afterCopy d 277 192 0 1
  have h2 := copy_run d1 243 193 (by decide) (by decide) (by decide)
    (by simpa [d1, afterCopy, StackRoutines.copyStacks] using h318)
  obtain ⟨nl, hnl, rl, hl⟩ := lowerCall_run localCode 225 244 (prepared d) _ K hlocal
  have he : Function.extend localPorts
      (Function.update ((prepared d).stacks ∘ localPorts) 244 output) (prepared d).stacks =
      Function.update (prepared d).stacks 244 output := by
    rw [ProgramLinking.extend_update localPorts.injective, lower_extend_project]
    rfl
  rw [he] at hl
  let d2 : Data := ⟨rl, Function.update (prepared d).stacks 244 output⟩
  have h3 := clearMany_run d2 [192,193]
  have hfinal : (SubexpSetupStorage.clearManyState [192,193] d2).stacks =
      Function.update d.stacks 244 output := by
    funext i
    by_cases h1 : i = 192 <;> by_cases h2 : i = 193 <;>
      simp [SubexpSetupStorage.clearManyState, SubexpSetupStorage.clearState,
        d2, prepared, afterCopy, StackRoutines.copyStacks, Function.update_apply,
        h1, h2, h192, h193]
  have heq : SubexpSetupStorage.clearManyState [192,193] d2 =
      (⟨(SubexpSetupStorage.clearManyState [192,193] d2).regs,
        Function.update d.stacks 244 output⟩ : Data) := state_ext rfl hfinal
  have hrun := h1.seq (h2.seq (hl.seq h3))
  rw [heq] at hrun
  refine ⟨_, ?_, _, hrun⟩
  simp [budget, d2, d1, prepared, afterCopy, StackRoutines.copyStacks,
    SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearState, h192, h193]
  omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Local

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

theorem lower_update_high (s : Fin 320 → List Bool) (j : Fin 320) (h : 256 ≤ j.val)
    (word : List Bool) : (Function.update s j word) ∘ localPorts = s ∘ localPorts := by
  funext i
  have hne : localPorts i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = j.val at hv
    omega
  simp [ hne]

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramMiddle
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Composition of the physical arithmetic stages for one Hermite node. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (LowFrame ServiceSpec)

theorem lowFrame_update_outer (s : Fin 320 → List Bool) (j : Fin 320) (hj : 205 ≤ j.val)
    (word : List Bool) : LowFrame (s ∘ localPorts) ((Function.update s j word) ∘ localPorts) := by
  intro i hi
  have hne : localPorts i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = j.val at hv
    omega
  simp [ hne]

theorem command_run_oai {C : Type*} (encode : C → List Bool)
    (localCode multiply add : Cmd 16 256) (mulOp addOp : C → C → C)
    (Km Ka Kl W J : ℕ) (d : Data) (remaining processed correction : List C)
    (unit minusOne zero node acc : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp Km)
    (ha : ServiceSpec (d.stacks ∘ localPorts) encode add addOp Ka)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (hr : d.stacks 257 = remaining.flatMap encode) (hp : d.stacks 258 = processed.flatMap encode)
    (hu : d.stacks 207 = encode unit) (hn : d.stacks 211 = encode minusOne)
    (hz : d.stacks 104 = encode zero) (hx : d.stacks 259 = encode node)
    (hacc : d.stacks 261 = encode acc) (hJ : d.stacks 243 = List.replicate J true)
    (hcorr : correction.length = J) (h277 : (d.stacks 277).length = J * W)
    (hc : ∀ i ∈ cleanPorts, d.stacks i = [])
    (hlocal : SubexpConvolutionControl.ExecutesIn localCode Kl
      ((Local.prepared d).stacks ∘ localPorts)
      (Function.update ((Local.prepared d).stacks ∘ localPorts) 244
        (HornerProgram.encodePolynomial encode correction))) :
    ∃ n ≤ budget (remaining.length + processed.length) J W Km Ka Kl, ∃ rf,
      Eval (command localCode multiply add) n d
        ⟨rf, Function.update d.stacks 261
          (encode (nodeValue mulOp addOp minusOne zero unit node acc J remaining processed correction))⟩ := by
  have hzero (i : Fin 320) (hi : i ∈ cleanPorts) := hc i hi
  have hco : ∀ i ∈ CofactorOuter.cleanPorts, d.stacks i = [] := by
    intro i hi; apply hc i; simp only [cleanPorts, List.mem_append]; tauto
  obtain ⟨n1, hn1, r1, h1⟩ := CofactorOuter.command_run encode multiply mulOp Km W J d
    remaining processed unit minusOne hm hw hW hr hp hu hn hJ (by simp [hz, hw]) hco
  let factor := (remaining ++ processed).foldl (Cofactor.includeValue mulOp minusOne J) unit
  let point := mulOp node minusOne
  let value := HornerProgram.fold (HornerProgram.stepValue mulOp addOp point) correction.reverse zero
  let d1 : Data := ⟨r1, Function.update d.stacks 262 (encode factor)⟩
  have hm1 : ServiceSpec (d1.stacks ∘ localPorts) encode multiply mulOp Km := by
    simpa only [d1, Scalar.lower_update_high d.stacks 262 (by decide)] using hm
  have hsc1 : ∀ i ∈ Scalar.cleanPorts, d1.stacks i = [] := by
    intro i hi
    simp only [Scalar.cleanPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [d1] using hc _ (by simp [cleanPorts, Scalar.cleanPorts])
  obtain ⟨n2, hn2, r2, h2⟩ := Scalar.negative_run encode multiply mulOp Km W d1 node minusOne
    hm1 hw (by simpa [d1] using hx) (by simpa [d1] using hn)
    (by simpa [d1] using hc 263 (by simp [cleanPorts])) hsc1
  let d2 : Data := ⟨r2, Function.update d1.stacks 263 (encode point)⟩
  have hpre : (Local.prepared d2).stacks ∘ localPorts = (Local.prepared d).stacks ∘ localPorts := by
    funext i
    have h262 : localPorts i ≠ (262 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 262 at hv; omega
    have h263 : localPorts i ≠ (263 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 263 at hv; omega
    simp [Local.prepared, d2, d1, afterCopy, StackRoutines.copyStacks,
 Function.update_apply, h262, h263]
  have hlocal2 : SubexpConvolutionControl.ExecutesIn localCode Kl
      ((Local.prepared d2).stacks ∘ localPorts)
      (Function.update ((Local.prepared d2).stacks ∘ localPorts) 244
        (HornerProgram.encodePolynomial encode correction)) := by simpa only [hpre] using hlocal
  obtain ⟨n3, hn3, r3, h3⟩ := Local.command_run localCode d2
    (HornerProgram.encodePolynomial encode correction) Kl
    (by simpa [d2, d1] using hc 192 (by simp [cleanPorts]))
    (by simpa [d2, d1] using hc 193 (by simp [cleanPorts]))
    (by simpa [d2, d1] using hc 318 (by simp [cleanPorts, Scalar.cleanPorts])) hlocal2
  let d3 : Data := ⟨r3, Function.update d2.stacks 244 (HornerProgram.encodePolynomial encode correction)⟩
  have hlow2 : d2.stacks ∘ localPorts = d.stacks ∘ localPorts := by
    simp only [d2, d1, Scalar.lower_update_high _ 263 (by decide), Scalar.lower_update_high _ 262 (by decide)]
  have hm3 : ServiceSpec (d3.stacks ∘ localPorts) encode multiply mulOp Km := by
    apply CRTLocalProgram.serviceSpec_frame (show ServiceSpec (d2.stacks ∘ localPorts) encode multiply mulOp Km by rw [hlow2]; exact hm)
    exact lowFrame_update_outer d2.stacks 244 (by decide) _
  have ha3 : ServiceSpec (d3.stacks ∘ localPorts) encode add addOp Ka := by
    apply CRTLocalProgram.serviceSpec_frame (show ServiceSpec (d2.stacks ∘ localPorts) encode add addOp Ka by rw [hlow2]; exact ha)
    exact lowFrame_update_outer d2.stacks 244 (by decide) _
  have hhc3 : ∀ i ∈ Horner.cleanPorts, d3.stacks i = [] := by
    intro i hi
    simp only [Horner.cleanPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [d3, d2, d1] using hc _ (by simp [cleanPorts, Horner.cleanPorts])
  obtain ⟨n4, hn4, r4, h4⟩ := Horner.command_run encode multiply add mulOp addOp Km Ka W d3
    correction point zero hm3 ha3 hw (by simp [d3]) (by simp [d3, d2])
    (by simpa [d3, d2, d1] using hz)
    (by simpa [d3, d2, d1, hJ] using hcorr.symm) hhc3
  let d4 : Data := ⟨r4, Function.update (Function.update d3.stacks 244 []) 264 (encode value)⟩
  have hlow4 : d4.stacks ∘ localPorts = d.stacks ∘ localPorts := by
    have hz244 : d.stacks 244 = [] := hc 244 (by simp [cleanPorts, Scalar.cleanPorts])
    funext i
    have h262 : localPorts i ≠ (262 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 262 at hv; omega
    have h263 : localPorts i ≠ (263 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 263 at hv; omega
    have h264 : localPorts i ≠ (264 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 264 at hv; omega
    by_cases h244 : localPorts i = (244 : Fin 320)
    · simp [d4, d3, d2, d1, h244, hz244]
    · simp [d4, d3, d2, d1, h244, h262, h263, h264]
  have hsc4 : ∀ i ∈ Scalar.cleanPorts, d4.stacks i = [] := by
    intro i hi
    have hci := hc i (by simp only [cleanPorts, List.mem_append]; tauto)
    simp only [Scalar.cleanPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [d4, d3, d2, d1, hci]
  obtain ⟨n5, hn5, r5, h5⟩ := Scalar.accumulate_run encode multiply add mulOp addOp Km Ka W d4
    acc factor value point (by rw [hlow4]; exact hm) (by rw [hlow4]; exact ha) hw
    (by simpa [d4, d3, d2, d1] using hacc) (by simp [d4, d3, d2, d1])
    (by simp [d4]) (by simp [d4, d3, d2]) hsc4
  have hfinal : Function.update (Function.update (Function.update (Function.update d4.stacks
        261 (encode (addOp acc (mulOp factor value)))) 262 []) 263 []) 264 [] =
      Function.update d.stacks 261 (encode (addOp acc (mulOp factor value))) := by
    funext i
    by_cases h244 : i = 244 <;> by_cases h262 : i = 262 <;>
      by_cases h263 : i = 263 <;> by_cases h264 : i = 264 <;>
      simp [d4, d3, d2, d1, Function.update_apply, h244, h262, h263, h264,
        hc 244 (by simp [cleanPorts, Scalar.cleanPorts]), hc 262 (by simp [cleanPorts]),
        hc 263 (by simp [cleanPorts]), hc 264 (by simp [cleanPorts])]
  rw [hfinal] at h5
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  refine ⟨_, ?_, r5, hrun⟩
  have hh277 : (d2.stacks 277).length = J * W := by simpa [d2, d1] using h277
  have hh243 : (d2.stacks 243).length = J := by simp [d2, d1, hJ]
  rw [hh277, hh243] at hn3
  rw [hcorr] at hn4
  unfold budget
  omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command_run_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command_run_oai.{u_1}

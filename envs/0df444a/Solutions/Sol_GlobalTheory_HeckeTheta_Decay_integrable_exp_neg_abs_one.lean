-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.Decay.integrable_exp_neg_abs_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:20:44.307278+00:00
-- url     : https://prove2.me/submissions/03815dcd-768b-46b4-ad23-65caca054aa3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeTheta GlobalTheory.HeckeTheta.Decay
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
namespace GlobalTheory.HeckeTheta.Decay
theorem _root_.solution : Integrable (fun x : ℝ => Real.exp (-1 * |x|)) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-1 * |x|)) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 one_pos).congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-1 * |x|)) (Set.Iic 0) :=
    (integrableOn_exp_mul_Iic one_pos 0).congr_fun (fun x hx => by rw [abs_of_nonpos hx, neg_mul_neg])
      measurableSet_Iic
  have h3 := h2.union h1
  rw [Set.Iic_union_Ioi, integrableOn_univ] at h3
  exact h3
end GlobalTheory.HeckeTheta.Decay

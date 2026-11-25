-- Prove2me | solution 1 for GlobalTheory.HermFrame.posDef_quotGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:45.828125+00:00
-- url     : https://prove2.me/submissions/8e6e920b-bc3f-4a68-ba95-226b883670ac

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_quotMap_mul_orthLift
import Theorems.Thm_GlobalTheory_HermFrame_form_orthLift
import Theorems.Thm_GlobalTheory_HermFrame_isHermitian_quotGram
import Theorems.Thm_GlobalTheory_HermFrame_posDef_subGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable [DecidableEq m] [DecidableEq l]
variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : H.PosDef) : (quotGram H).PosDef := by
  have hu : IsUnit (subGram H).det := (isUnit_iff_isUnit_det _).1 (posDef_subGram h).isUnit
  refine posDef_iff.2 ⟨isHermitian_quotGram h.isHermitian, fun q hq => ?_⟩
  rw [← form_orthLift hu]
  refine (posDef_iff.1 h).2 _ fun h0 => hq ?_
  rw [← one_mulVec q, ← quotMap_mul_orthLift H, ← mulVec_mulVec, h0, mulVec_zero]
end GlobalTheory.HermFrame

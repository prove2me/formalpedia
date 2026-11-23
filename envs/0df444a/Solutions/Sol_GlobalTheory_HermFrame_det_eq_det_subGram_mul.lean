-- Prove2me | solution 1 for GlobalTheory.HermFrame.det_eq_det_subGram_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:52.944357+00:00
-- url     : https://prove2.me/submissions/2b8e0123-07fe-4cfb-8071-7bcafaefc8bd

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale

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
theorem _root_.solution (hu : IsUnit (subGram H).det) :
    H.det = (subGram H).det * (quotGram H).det := by
  letI : Invertible H.toBlocks₁₁ := invertibleOfIsUnitDet _ hu
  conv_lhs => rw [← fromBlocks_toBlocks H]
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]; rfl
end GlobalTheory.HermFrame

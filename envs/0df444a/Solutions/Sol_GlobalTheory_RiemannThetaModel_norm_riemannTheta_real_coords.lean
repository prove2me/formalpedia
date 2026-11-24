-- Prove2me | solution 1 for GlobalTheory.RiemannThetaModel.norm_riemannTheta_real_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:56:30.741502+00:00
-- url     : https://prove2.me/submissions/8969b90f-e9a5-40a8-9daf-b368c210769d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.RiemannThetaModel
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.RiemannThetaModel
theorem _root_.solution {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (a b x y : ι → ℝ) :
    ‖riemannTheta a b Ω ((fun i => (x i : ℂ)) + Ω *ᵥ fun i => (y i : ℂ))‖ =
      Real.exp (π * (y ⬝ᵥ (Ω.map Complex.im *ᵥ y))) * ‖riemannTheta (a + y) (b + x) Ω 0‖ := by
  rw [riemannTheta_add_mulVec_ofReal h, norm_mul, Complex.norm_exp,
    ← riemannTheta_add_ofReal, zero_add]
  congr 2
  simp [dotProduct, mulVec, Finset.mul_sum _ _ (y _ : ℂ), Finset.mul_sum _ _ (y _ : ℝ)]
  ring
end GlobalTheory.RiemannThetaModel

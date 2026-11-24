-- Prove2me | solution 1 for GlobalTheory.RiemannThetaModel.riemannTheta_zero_zero_half_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:55.961985+00:00
-- url     : https://prove2.me/submissions/b6a8b5c1-676b-4356-b98c-cf27d3faa7d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic
import Theorems.Thm_GlobalTheory_riemannTheta_eq_cexp_mul_zero_zero


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
theorem _root_.solution (τ : ℂ) :
    riemannTheta 0 0 !![τ] ![(1 + τ) / 2] = 0 := by
  have hs : (!![τ] : Matrix (Fin 1) (Fin 1) ℂ).IsSymm := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have h0 : riemannTheta (fun _ : Fin 1 => ((1 : ℤ) : ℝ) / 2) (fun _ => ((1 : ℤ) : ℝ) / 2)
      !![τ] 0 = 0 := by
    have := riemannTheta_half_neg (fun _ : Fin 1 => 1) (fun _ => 1) !![τ] 0
    simp only [neg_zero, dotProduct, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, one_smul, zpow_one] at this
    linear_combination this / 2
  rw [riemannTheta_eq_cexp_mul_zero_zero hs, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Complex.exp_ne_zero _)
  · convert h0 using 2
    funext i
    fin_cases i
    simp [dotProduct]
    ring
end GlobalTheory.RiemannThetaModel

-- Prove2me | solution 1 for GlobalTheory.theta_value_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:13:55.678144+00:00
-- url     : https://prove2.me/submissions/6d88048a-f1e8-4134-95b2-56f3f9cad4f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_GlobalTheory_ThetaBound_pointwiseNormSq_le_l2_of_firstMinimum
import Theorems.Thm_GlobalTheory_translate_jet_bound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open Classical
namespace GlobalTheory
theorem _root_.solution (hsup : GSupStatement) {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (Y : GT ι) (F : EuclideanSpace ℂ ι → ℂ) (hF : F ∈ Y.Sec 1) (lam : ℝ) (hlam : 0 < lam) (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖)
    {κ : Type} (s : Finset κ) (c : κ → ℂ) (hc : ∀ j ∈ s, ‖c j‖ ≤ 1) (y : κ → EuclideanSpace ℂ ι)
    (P : MvPolynomial ι ℂ) (a : ℕ) (hP : P.IsHomogeneous a) :
    ‖∑ j ∈ s, c j * polyDeriv P (fun i => EuclideanSpace.single i 1) (U 1 (y j) F) 0‖ ≤
      s.card * (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) / (Real.sqrt Real.pi * lam)) ^ Fintype.card ι) * Real.sqrt (Y.l2 1 F) := by
  set C : ℝ := Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) /
    (Real.sqrt Real.pi * lam)) ^ Fintype.card ι with hC
  have hC0 : 0 ≤ C := by positivity
  have key : ∀ j ∈ s,
      ‖c j * polyDeriv P (fun i => EuclideanSpace.single i 1) (U 1 (y j) F) 0‖ ≤
        (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) * C *
          Real.sqrt (Y.l2 1 F) := by
    intro j hj
    have h := translate_jet_bound U hU 1 le_rfl F hF.1 (C ^ 2 * Y.l2 1 F)
      (ThetaBound.pointwiseNormSq_le_l2_of_firstMinimum hsup Y hF hlam hmin) P a hP (y j)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC0, Nat.cast_one, one_mul] at h
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hc j hj)).trans (h.trans_eq ?_)
    ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ key).trans_eq ?_)
  rw [nsmul_eq_mul]
  ring
end GlobalTheory

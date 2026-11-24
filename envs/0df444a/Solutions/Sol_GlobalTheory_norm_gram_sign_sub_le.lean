-- Prove2me | solution 1 for GlobalTheory.norm_gram_sign_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:27:13.707795+00:00
-- url     : https://prove2.me/submissions/10b782e1-c129-4c2b-909a-602300e32d5b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {r : ℕ} (j : Fin r → ℂ) (hj : ∀ a, ‖j a‖ = 1)
    (z : Matrix (Fin r) (Fin r) ℂ) {δ : ℝ} (hδ : 0 ≤ δ) (hr : r * δ ≤ 1) (hz : ∀ a b, ‖z a b‖ ≤ δ)
    (a b : Fin r) :
    ‖((1 + z)ᵀ * diagonal j * (1 + z).map star - diagonal j : Matrix (Fin r) (Fin r) ℂ) a b‖ ≤ 3 * δ := by
  have hstar : (1 + z : Matrix (Fin r) (Fin r) ℂ).map star = 1 + z.map star := by
    ext a b
    by_cases h : a = b <;> simp [one_apply, h]
  have heq : (1 + z)ᵀ * diagonal j * (1 + z).map star - diagonal j =
      zᵀ * diagonal j + diagonal j * z.map star + zᵀ * diagonal j * z.map star := by
    rw [hstar]
    simp only [transpose_add, transpose_one]
    noncomm_ring
  rw [heq, Matrix.add_apply, Matrix.add_apply]
  have h1 : ∀ a b, ‖(zᵀ * diagonal j) a b‖ ≤ δ := fun a b => by
    rw [mul_diagonal, norm_mul, hj, mul_one]; exact hz _ _
  have h2 : ‖(diagonal j * z.map star) a b‖ ≤ δ := by
    rw [diagonal_mul, norm_mul, hj, one_mul, map_apply, norm_star]; exact hz _ _
  have h3 : ‖(zᵀ * diagonal j * z.map star) a b‖ ≤ r * (δ * δ) := by
    rw [mul_apply]
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul Finset.univ
      (fun k => ‖(zᵀ * diagonal j) a k * z.map star k b‖) (δ * δ) fun k _ => by
        rw [norm_mul, map_apply, norm_star]
        exact mul_le_mul (h1 _ _) (hz _ _) (norm_nonneg _) hδ
    simpa using this
  refine norm_add₃_le.trans ?_
  nlinarith [h1 a b]
end GlobalTheory

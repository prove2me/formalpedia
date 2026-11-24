-- Prove2me | solution 1 for GlobalTheory.UnramifiedHensel.taylor_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:20:22.546297+00:00
-- url     : https://prove2.me/submissions/6ad7b1b3-dbbf-4e19-89a6-7dc7ccc6317d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRelationGradient
import Theorems.Thm_GlobalTheory_UnramifiedHensel_norm_eval_le_one
import Theorems.Thm_GlobalTheory_UnramifiedHensel_norm_sum_le_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.UnramifiedHensel
variable {K : Type} [NormedField K] [IsUltrametricDist K] {R ι : Type} [CommRing R]
namespace GlobalTheory.UnramifiedHensel
theorem _root_.solution [Fintype ι] [DecidableEq ι] (c : R →+* K) (hc : ∀ w, ‖c w‖ ≤ 1)
    (x y : ι → K) (hx : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1) {r : ℝ} (hr : 0 ≤ r)
    (hxy : ∀ i, ‖y i - x i‖ ≤ r) (G : MvPolynomial ι R) :
    ‖eval₂ c y G - eval₂ c x G - ∑ j, eval₂ c x (pderiv j G) * (y j - x j)‖ ≤ r * r := by
  induction G using MvPolynomial.induction_on with
  | C a => simpa using mul_nonneg hr hr
  | add p q hp hq =>
    have : eval₂ c y (p + q) - eval₂ c x (p + q) -
        ∑ j, eval₂ c x (pderiv j (p + q)) * (y j - x j) =
        (eval₂ c y p - eval₂ c x p - ∑ j, eval₂ c x (pderiv j p) * (y j - x j)) +
        (eval₂ c y q - eval₂ c x q - ∑ j, eval₂ c x (pderiv j q) * (y j - x j)) := by
      simp only [map_add, eval₂_add, add_mul, Finset.sum_add_distrib]; ring
    rw [this]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hp hq)
  | mul_X p n hp =>
    have h1 : ∀ j, eval₂ c x (pderiv j (p * X n)) * (y j - x j) =
        eval₂ c x (pderiv j p) * (y j - x j) * x n +
          (if j = n then eval₂ c x p * (y n - x n) else 0) := by
      intro j
      rw [pderiv_mul, pderiv_X]
      by_cases hj : j = n
      · subst hj; simp [eval₂_mul]; ring
      · simp [hj, Pi.single_apply, Ne.symm hj, eval₂_mul]; ring
    have hL : ‖∑ j, eval₂ c x (pderiv j p) * (y j - x j)‖ ≤ r := by
      refine norm_sum_le_of_le _ hr fun j => ?_
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_eval_le_one c hc x hx _)).trans (hxy j)
    have : eval₂ c y (p * X n) - eval₂ c x (p * X n) -
        ∑ j, eval₂ c x (pderiv j (p * X n)) * (y j - x j) =
        y n * (eval₂ c y p - eval₂ c x p - ∑ j, eval₂ c x (pderiv j p) * (y j - x j)) +
        (y n - x n) * ∑ j, eval₂ c x (pderiv j p) * (y j - x j) := by
      simp only [h1, Finset.sum_add_distrib, ← Finset.sum_mul, eval₂_mul, eval₂_X]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hy n)).trans hp
    · rw [norm_mul]
      exact mul_le_mul (hxy n) hL (norm_nonneg _) hr
end GlobalTheory.UnramifiedHensel

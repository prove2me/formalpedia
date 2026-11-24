-- Prove2me | solution 1 for GlobalTheory.WeightedLS.weighted_least_squares_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:24:38.057872+00:00
-- url     : https://prove2.me/submissions/0c6085d2-2d72-4b09-a9fa-ff619249cae0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBound
import Theorems.Thm_GlobalTheory_WeightedLS_det_pos
import Theorems.Thm_GlobalTheory_WeightedLS_det_eq_sum
import Theorems.Thm_GlobalTheory_WeightedLS_block_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory GlobalTheory.WeightedLS
open Matrix
variable {M g : ℕ}
namespace GlobalTheory.WeightedLS
theorem _root_.solution : ∀ (M g : ℕ) (L : Matrix (Fin M) (Fin g) ℝ), L.rank = g →
    ∃ K : ℝ, ∀ (D : Fin M → ℝ) (b : Fin M → ℝ), (∀ k, 0 < D k) →
      ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖ ≤
        K * ‖b‖ := by
  intro M g L hL
  choose K hK0 hK using fun S : {S : Finset (Fin M) // S.card = g} =>
    block_bound (L.submatrix (S.1.orderEmbOfFin S.2) id)
  refine ⟨∑ S, K S, fun D b hD => ?_⟩
  have hKs : 0 ≤ ∑ S, K S := Finset.sum_nonneg fun S _ => hK0 S
  have hdet := det_pos L hL D hD
  set A := L.transpose * Matrix.diagonal D * L with hA
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
  have hx : A.det * (A⁻¹ * L.transpose * Matrix.diagonal D).mulVec b k =
      (L.transpose * Matrix.diagonal D * L.updateCol k b).det := by
    have h1 := Matrix.det_smul_inv_mulVec_eq_cramer A ((L.transpose * Matrix.diagonal D).mulVec b)
      (isUnit_iff_ne_zero.mpr hdet.ne')
    have h2 := congrFun h1 k
    rw [Matrix.cramer_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at h2
    rw [← smul_eq_mul, ← Pi.smul_apply, h2]
    congr 1
    ext i j
    by_cases hj : j = k
    · subst hj
      simp [Matrix.mul_apply (M := L.transpose * Matrix.diagonal D), Matrix.mulVec, dotProduct]
    · simp [hA, Matrix.mul_apply (M := L.transpose * Matrix.diagonal D), Matrix.updateCol_ne hj]
  have hb : |(L.transpose * Matrix.diagonal D * L.updateCol k b).det| ≤
      (∑ S, K S) * ‖b‖ * A.det := by
    rw [hA, det_eq_sum, det_eq_sum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S _ => ?_)
    set e := S.1.orderEmbOfFin S.2 with he
    have hp : 0 ≤ ∏ j, D (e j) := Finset.prod_nonneg fun j _ => (hD _).le
    have hu : (L.updateCol k b).submatrix e id = (L.submatrix e id).updateCol k (b ∘ e) := by
      ext i j
      by_cases hj : j = k
      · subst hj; simp
      · simp [Matrix.updateCol_ne hj]
    have hn : ‖b ∘ e‖ ≤ ‖b‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm b (e i)
    have hKS : K S ≤ ∑ S, K S :=
      Finset.single_le_sum (f := K) (fun S _ => hK0 S) (Finset.mem_univ S)
    rw [abs_mul, abs_of_nonneg hp, hu, mul_left_comm]
    refine mul_le_mul_of_nonneg_left ((hK S (b ∘ e) k).trans ?_) hp
    exact mul_le_mul_of_nonneg_right (mul_le_mul hKS hn (norm_nonneg _) hKs) (mul_self_nonneg _)
  rw [← hx, abs_mul, abs_of_pos hdet, mul_comm] at hb
  exact le_of_mul_le_mul_right hb hdet
end GlobalTheory.WeightedLS

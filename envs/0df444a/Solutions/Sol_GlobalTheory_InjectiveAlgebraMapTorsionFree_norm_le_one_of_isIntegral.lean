-- Prove2me | solution 1 for GlobalTheory.InjectiveAlgebraMapTorsionFree.norm_le_one_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:03:07.735846+00:00
-- url     : https://prove2.me/submissions/083961a0-6254-4fec-99ee-62d8d934d595

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOne
import Theorems.Thm_GlobalTheory_InjectiveAlgebraMapTorsionFree_norm_algebraMap_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InjectiveAlgebraMapTorsionFree
variable (p : ℕ) [Fact (Nat.Prime p)]
namespace GlobalTheory.InjectiveAlgebraMapTorsionFree
theorem _root_.solution (x : PadicAlgCl p) (hx : IsIntegral ℤ_[p] x) : ‖x‖ ≤ 1 := by
  haveI : IsUltrametricDist (PadicAlgCl p) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicAlgCl.isNonarchimedean p)
  by_contra h
  push_neg at h
  obtain ⟨q, hqm, hq⟩ := hx
  rw [hqm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at hq
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hq
  have hxn : x ^ q.natDegree =
      -∑ i ∈ Finset.range q.natDegree, algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left hq
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | hn
  · rw [h0] at hxn
    simp at hxn
  have hx1 : 1 ≤ ‖x‖ := h.le
  have hle : ‖∑ i ∈ Finset.range q.natDegree, algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i) * x ^ i‖ ≤
      ‖x‖ ^ (q.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (norm_nonneg _) _)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' := Finset.mem_range.mp hi
    calc ‖algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (q.natDegree - 1) :=
          mul_le_mul (norm_algebraMap_le p _) (pow_le_pow_right₀ hx1 (by omega))
            (pow_nonneg (norm_nonneg _) _) zero_le_one
      _ = ‖x‖ ^ (q.natDegree - 1) := one_mul _
  have h1 : ‖x‖ ^ q.natDegree ≤ ‖x‖ ^ (q.natDegree - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    exact hle
  have h2 : ‖x‖ ^ (q.natDegree - 1) < ‖x‖ ^ q.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith
end GlobalTheory.InjectiveAlgebraMapTorsionFree

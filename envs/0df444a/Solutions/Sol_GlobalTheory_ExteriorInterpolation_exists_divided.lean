-- Prove2me | solution 1 for GlobalTheory.ExteriorInterpolation.exists_divided
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:13:47.717694+00:00
-- url     : https://prove2.me/submissions/90e29188-fb31-4766-a31b-39938bfbed60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsInterpolationExteriorSmallCoeffs
import Theorems.Thm_GlobalTheory_ExteriorInterpolation_exists_coeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExteriorInterpolation
namespace GlobalTheory.ExteriorInterpolation
theorem _root_.solution (l : ℕ) (z : Fin l → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∃ b : Fin l → ℂ → ℂ, (∀ j, Continuous (b j)) ∧ (∀ j ζ, ‖ζ‖ ≤ 1 → ‖b j ζ‖ ≤ 2 ^ l) ∧
      ∀ ζ w : ℂ, (∑ j, b j ζ * w ^ (j : ℕ)) * (ζ - w) = ∏ i, (ζ - z i) - ∏ i, (w - z i) := by
  obtain ⟨a, ha, hsum⟩ := exists_coeffs l z hz
  refine ⟨fun j ζ => ∑ k ∈ Finset.range (l + 1),
    if (j : ℕ) < k then a k * ζ ^ (k - 1 - j) else 0, ?_, ?_, ?_⟩
  · intro j
    exact continuous_finsetSum _ (fun k _ => by split_ifs <;> fun_prop)
  · intro j ζ hζ
    calc ‖∑ k ∈ Finset.range (l + 1), if (j : ℕ) < k then a k * ζ ^ (k - 1 - j) else 0‖
        ≤ ∑ k ∈ Finset.range (l + 1), ‖a k‖ := by
          apply norm_sum_le_of_le
          intro k _
          split_ifs
          · rw [norm_mul, norm_pow]
            exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hζ)
          · simp
      _ ≤ 2 ^ l := hsum
  · intro ζ w
    rw [ha ζ, ha w, ← Finset.sum_sub_distrib]
    have e1 : (∑ j : Fin l, (∑ k ∈ Finset.range (l + 1),
          if (j : ℕ) < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ (j : ℕ))
        = ∑ k ∈ Finset.range (l + 1), ∑ j ∈ Finset.range l,
          (if j < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ j := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (∑ k ∈ Finset.range (l + 1),
        if j < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ j) l]
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    rw [e1, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkl : k ≤ l := by simpa [Nat.lt_succ_iff] using hk
    have e2 : ∑ j ∈ Finset.range l, (if j < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ j
        = a k * ∑ j ∈ Finset.range k, w ^ j * ζ ^ (k - 1 - j) := by
      rw [Finset.mul_sum,
        show Finset.range k = (Finset.range l).filter (· < k) by ext j; simp; omega,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    have e3 : (∑ j ∈ Finset.range k, w ^ j * ζ ^ (k - 1 - j)) * (ζ - w) = ζ ^ k - w ^ k := by
      rw [← neg_sub w ζ, mul_neg, geom_sum₂_mul]
      ring
    rw [e2, mul_assoc, e3]
    ring
end GlobalTheory.ExteriorInterpolation

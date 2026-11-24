-- Prove2me | solution 1 for GlobalTheory.exists_choose_rpow_le_norm_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:34.075722+00:00
-- url     : https://prove2.me/submissions/46b0cb96-5328-4c10-a57a-d7c3d5f579ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Theorems.Thm_GlobalTheory_sum_norm_sq_minors_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
namespace GlobalTheory
theorem _root_.solution (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    i ≤ Fintype.card n ∧ ∃ S : Set.powersetCard n i,
      ((Fintype.card n).choose i : ℝ) ^ (-(1 : ℝ) / 2) ≤
        ‖(A.submatrix id (subsetEnum S)).det‖ := by
  have h := sum_norm_sq_minors_eq_one A hA
  have hne : (Finset.univ : Finset (Set.powersetCard n i)).Nonempty := by
    rcases (Finset.univ : Finset (Set.powersetCard n i)).eq_empty_or_nonempty with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  have hi : i ≤ Fintype.card n := by
    obtain ⟨S, -⟩ := hne
    exact S.2 ▸ Finset.card_le_univ S.1
  have hcard : Fintype.card (Set.powersetCard n i) = (Fintype.card n).choose i := by
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card]
  have hpos : (0 : ℝ) < (Fintype.card n).choose i := by exact_mod_cast Nat.choose_pos hi
  refine ⟨hi, ?_⟩
  obtain ⟨S, -, hS⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => (((Fintype.card n).choose i : ℝ))⁻¹)
    (g := fun S => ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2) (by
      rw [h, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_inv_cancel₀ hpos.ne'])
  refine ⟨S, (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_⟩
  refine le_of_eq_of_le ?_ hS
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_neg_one]
  norm_num
end GlobalTheory

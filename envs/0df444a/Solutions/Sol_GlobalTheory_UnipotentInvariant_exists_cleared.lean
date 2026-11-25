-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.exists_cleared
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:12:38.568978+00:00
-- url     : https://prove2.me/submissions/34c1e3d1-5b22-423f-b9de-5fdb4c3dab7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
import Theorems.Thm_GlobalTheory_UnipotentInvariant_BiInvariant_transpose
import Theorems.Thm_GlobalTheory_UnipotentInvariant_biInvariant_leadMinor
import Theorems.Thm_GlobalTheory_UnipotentInvariant_exists_clear_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}
namespace GlobalTheory.UnipotentInvariant
theorem _root_.solution (M : Matrix (Fin p) (Fin p) K) (hM : ∀ i, leadMinor i M ≠ 0) (n : ℕ) :
    ∃ M' : Matrix (Fin p) (Fin p) K, (∀ f, BiInvariant f → f M' = f M) ∧
      ∀ i j : Fin p, i ≠ j → (i.val < n ∨ j.val < n) → M' i j = 0 := by
  induction n with
  | zero => exact ⟨M, fun _ _ => rfl, by simp⟩
  | succ n ih =>
    obtain ⟨M₀, h₀, hz₀⟩ := ih
    by_cases hn : n < p
    swap
    · exact ⟨M₀, h₀, fun i j hij _ => hz₀ i j hij (Or.inl (by omega))⟩
    set N : Fin p := ⟨n, hn⟩ with hN
    have hpiv : M₀ N N ≠ 0 := by
      intro h0
      apply hM N
      rw [← h₀ _ (biInvariant_leadMinor N)]
      unfold leadMinor
      apply det_eq_zero_of_row_eq_zero (Fin.last n)
      intro j
      simp only [of_apply]
      by_cases hj : j = Fin.last n
      · subst hj
        exact h0
      · apply hz₀
        · intro h
          apply hj
          ext
          simpa using (congrArg Fin.val h).symm
        · right
          exact Fin.val_lt_last hj
    obtain ⟨M₁, h₁, a₁, b₁, c₁⟩ := exists_clear_col N M₀ hpiv
    have hpiv₁ : M₁ᵀ N N ≠ 0 := by
      rw [transpose_apply, b₁ N N le_rfl]
      exact hpiv
    obtain ⟨M₂, h₂, a₂, b₂, c₂⟩ := exists_clear_col N M₁ᵀ hpiv₁
    have hz₁ : ∀ i j : Fin p, i ≠ j → (i.val < n ∨ j.val < n) → M₁ i j = 0 := by
      intro i j hij h
      rcases h with h | h
      · rw [b₁ i j (by simp [Fin.le_def, hN]; omega)]
        exact hz₀ i j hij (Or.inl h)
      · rw [c₁ i j (hz₀ N j (by intro hh; rw [← hh] at h; simp [hN] at h) (Or.inr h))]
        exact hz₀ i j hij (Or.inr h)
    have hcol : ∀ i : Fin p, i ≠ N → M₁ i N = 0 := by
      intro i hi
      rcases lt_or_gt_of_ne hi with h | h
      · exact hz₁ i N hi (Or.inl h)
      · exact a₁ i h
    refine ⟨M₂ᵀ, fun f hf => ?_, ?_⟩
    · have := h₂ _ hf.transpose
      simp only [transpose_transpose] at this
      rw [this, h₁ f hf, h₀ f hf]
    · intro i j hij h
      rw [transpose_apply]
      by_cases hj : j ≤ N
      · rw [b₂ j i hj, transpose_apply]
        rcases eq_or_lt_of_le hj with hj | hj
        · subst hj
          exact hcol i hij
        · exact hz₁ i j hij (Or.inr hj)
      · have hj' : N < j := not_le.mp hj
        have hi : i.val < n + 1 := by
          rcases h with h | h
          · exact h
          · exact absurd hj' (by simp [Fin.lt_def, hN]; omega)
        by_cases hiN : i = N
        · subst hiN
          exact a₂ j hj'
        · rw [c₂ j i (hcol i hiN), transpose_apply]
          refine hz₁ i j hij (Or.inl ?_)
          have : i.val ≠ n := fun hh => hiN (Fin.ext hh)
          omega
end GlobalTheory.UnipotentInvariant

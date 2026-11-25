-- Prove2me | solution 1 for GlobalTheory.UnramValue.norm_rootRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:23:48.996577+00:00
-- url     : https://prove2.me/submissions/9d223b20-7aef-4a3c-b7fe-41ea74fb398c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
import Theorems.Thm_GlobalTheory_UnramValue_norm_l
import Theorems.Thm_GlobalTheory_UnramValue_norm_le_one
import Theorems.Thm_GlobalTheory_UnramValue_exists_eq_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.UnramValue
theorem _root_.solution {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m) {y : Om l} (hy : y ∈ rootRing l m)
    (h0 : y ≠ 0) : ∃ n : ℤ, ‖y‖ = (l : ℝ) ^ n := by
  have hp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have key : ∀ k : ℕ, ∀ y ∈ rootRing l m, y ≠ 0 → (l : ℝ) ^ (-(k : ℤ)) ≤ ‖y‖ →
      ∃ n : ℤ, ‖y‖ = (l : ℝ) ^ n := by
    intro k
    induction k with
    | zero =>
      intro y hy _ hle
      refine ⟨0, ?_⟩
      simp only [Nat.cast_zero, neg_zero, zpow_zero] at hle ⊢
      exact le_antisymm (norm_le_one hm hy) hle
    | succ k ih =>
      intro y hy hy0 hle
      rcases (norm_le_one hm hy).lt_or_eq with hlt | heq
      · obtain ⟨z, hz, rfl⟩ := exists_eq_mul hm hl hy hlt
        have hz0 : z ≠ 0 := by rintro rfl; simp at hy0
        rw [norm_mul, norm_l] at hle ⊢
        rw [show (-((k + 1 : ℕ) : ℤ)) = -(k : ℤ) - 1 by push_cast; ring,
          zpow_sub_one₀ hl0.ne'] at hle
        have hk : (l : ℝ) ^ (-(k : ℤ)) ≤ ‖z‖ :=
          le_of_mul_le_mul_left (by rwa [mul_comm] at hle) (inv_pos.2 hl0)
        obtain ⟨n, hn⟩ := ih z hz hz0 hk
        exact ⟨n - 1, by rw [hn, zpow_sub_one₀ hl0.ne', mul_comm]⟩
      · exact ⟨0, by simp [heq]⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (l : ℝ) ^ (-(k : ℤ)) ≤ ‖y‖ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 h0) (inv_lt_one_of_one_lt₀ hl1)
    exact ⟨k, by rw [zpow_neg, zpow_natCast, ← inv_pow]; exact hk.le⟩
  exact key k y hy h0 hk
end GlobalTheory.UnramValue

-- Prove2me | solution 1 for GlobalTheory.Cyc.norm_unit_zpow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:54.524385+00:00
-- url     : https://prove2.me/submissions/8d2c1fdc-00b9-42b9-9390-85648fac7e5c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneOfNotDvd
import Theorems.Thm_GlobalTheory_Cyc_norm_pow_nat_sub_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution :
    ∀ (l : ℕ) [Fact l.Prime], ∀ (s : ℕ) (u : ℤ_[l]ˣ), 1 ≤ s → (l = 2 → 2 ≤ s) →
      ‖(u : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) → ∀ n : ℤ, n ≠ 0 →
      ‖((u ^ n : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) * ‖(n : ℤ_[l])‖ := by
  intro l hl s u hs h2 hu n hn
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hx : ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ)⁻¹ := by
    rw [hu, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1.le (by omega)
  have hx2 : l = 2 → ‖(u : ℤ_[l]) - 1‖ < (l : ℝ)⁻¹ := fun h => by
    have := h2 h
    rw [hu, ← zpow_neg_one]
    exact zpow_lt_zpow_right₀ hl1 (by omega)
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · have hm : m ≠ 0 := by rintro rfl; simp at hn
    rw [zpow_natCast, Units.val_pow_eq_pow_val, norm_pow_nat_sub_one m hm _ hx hx2, hu,
      Int.cast_natCast]
  · have hm : m ≠ 0 := by rintro rfl; simp at hn
    have e : (((u ^ m)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1
        = -((((u ^ m)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (((u ^ m : ℤ_[l]ˣ) : ℤ_[l]) - 1)) := by
      rw [mul_sub, Units.inv_mul]; ring
    rw [zpow_neg, zpow_natCast, e, norm_neg, norm_mul, PadicInt.norm_units, one_mul,
      Units.val_pow_eq_pow_val, norm_pow_nat_sub_one m hm _ hx hx2, hu, Int.cast_neg, norm_neg,
      Int.cast_natCast]
end GlobalTheory.Cyc

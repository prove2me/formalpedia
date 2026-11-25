-- Prove2me | solution 1 for GlobalTheory.Cyc.norm_pow_prime_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:31.859264+00:00
-- url     : https://prove2.me/submissions/79aebfe0-e575-4beb-b9fe-c3ee37aa899b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneOfNotDvd
import Theorems.Thm_GlobalTheory_Cyc_geom_sum_one_add_expand
import Theorems.Thm_GlobalTheory_Cyc_padicInt_norm_add_eq_of_lt

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
theorem _root_.solution (x : ℤ_[l]) (hx : ‖x - 1‖ ≤ (l : ℝ)⁻¹)
    (h2 : l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) :
    ‖x ^ l - 1‖ = ‖x - 1‖ * ‖(l : ℤ_[l])‖ := by
  obtain ⟨z, hz⟩ := geom_sum_one_add_expand (x - 1) l
  rw [add_sub_cancel] at hz
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hi0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hsq : (l : ℝ)⁻¹ * (l : ℝ)⁻¹ < (l : ℝ)⁻¹ := mul_lt_of_lt_one_right hi0 hi1
  have hA : ‖((l.choose 2 : ℕ) : ℤ_[l]) * (x - 1)‖ < (l : ℝ)⁻¹ := by
    rw [norm_mul]
    by_cases h : l = 2
    · exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)) (h2 h)
    · have hlt : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h)
      obtain ⟨c, hc⟩ := hl.out.dvd_choose_self (k := 2) (by norm_num) hlt
      have : ‖((l.choose 2 : ℕ) : ℤ_[l])‖ ≤ (l : ℝ)⁻¹ := by
        rw [hc, Nat.cast_mul, norm_mul, PadicInt.norm_p]
        exact mul_le_of_le_one_right hi0.le (PadicInt.norm_le_one _)
      exact lt_of_le_of_lt (mul_le_mul this hx (norm_nonneg _) hi0.le) hsq
  have hB : ‖(x - 1) ^ 2 * z‖ < (l : ℝ)⁻¹ := by
    rw [norm_mul, sq, norm_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)) ?_
    exact lt_of_le_of_lt (mul_le_mul hx hx (norm_nonneg _) hi0.le) hsq
  rw [hz, norm_mul, add_assoc, padicInt_norm_add_eq_of_lt]
  rw [PadicInt.norm_p]
  exact lt_of_le_of_lt (PadicInt.nonarchimedean _ _) (max_lt hA hB)
end GlobalTheory.Cyc

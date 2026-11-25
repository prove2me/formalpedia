-- Prove2me | solution 1 for GlobalTheory.Cyc.norm_pow_nat_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:36:13.177486+00:00
-- url     : https://prove2.me/submissions/a81db153-e416-4783-b7ad-308283630aff

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneOfNotDvd
import Theorems.Thm_GlobalTheory_Cyc_norm_pow_sub_one_of_not_dvd
import Theorems.Thm_GlobalTheory_Cyc_norm_pow_prime_sub_one

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
theorem _root_.solution (n : ℕ) (hn : n ≠ 0) : ∀ (x : ℤ_[l]), ‖x - 1‖ ≤ (l : ℝ)⁻¹ →
    (l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) → ‖x ^ n - 1‖ = ‖x - 1‖ * ‖(n : ℤ_[l])‖ := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx h2
    by_cases hd : l ∣ n
    · obtain ⟨m, rfl⟩ := hd
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      have hlt : m < l * m := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm) hl.out.one_lt
      have key := norm_pow_prime_sub_one x hx h2
      have hle : ‖x ^ l - 1‖ ≤ ‖x - 1‖ := by
        rw [key]; exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
      rw [pow_mul, ih m hlt hm (x ^ l) (hle.trans hx) (fun h => hle.trans_lt (h2 h)), key,
        Nat.cast_mul, norm_mul, mul_assoc]
    · have hn1 : ‖(n : ℤ_[l])‖ = 1 := by
        apply le_antisymm (PadicInt.norm_le_one _)
        by_contra h
        push_neg at h
        have h' : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
        rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
        exact hd (Int.natCast_dvd_natCast.mp h')
      rw [norm_pow_sub_one_of_not_dvd x (hx.trans_lt hi1) n hd, hn1, mul_one]
end GlobalTheory.Cyc

-- Prove2me | solution 1 for GlobalTheory.Cyc.exists_norm_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:26:56.407803+00:00
-- url     : https://prove2.me/submissions/7f2e06b6-7429-45d7-a850-ce78bfb89f4d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValIntStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Theorems.Thm_GlobalTheory_Cyc_norm_pow_sub_lin_le
import Theorems.Thm_GlobalTheory_Cyc_exists_nat_norm_sub_le
import Theorems.Thm_GlobalTheory_Cyc_norm_pow_pow_sub_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution (j : ℕ) (hj : Lev l j) (u s : ℚ_[l]) (hu1 : ‖u‖ = 1)
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (hs : ‖s - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) (m : ℕ) :
    ∃ a : ℕ, ‖s - u ^ a‖ ≤ (l : ℝ) ^ (-((j + m : ℕ) : ℤ)) := by
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  induction m with
  | zero => exact ⟨0, by simpa using hs⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih
    set w := u ^ (l ^ m) with hw
    have hw1 : ‖w‖ = 1 := by rw [hw, norm_pow, hu1, one_pow]
    have hd : ‖w - 1‖ = (l : ℝ) ^ (-((j + m : ℕ) : ℤ)) := norm_pow_pow_sub_one j hj u hu m
    have hdpos : 0 < ‖w - 1‖ := by rw [hd]; positivity
    have hd0 : w - 1 ≠ 0 := norm_pos_iff.1 hdpos
    set t := u ^ a with ht
    have ht1 : ‖t‖ = 1 := by rw [ht, norm_pow, hu1, one_pow]
    have ht0 : t ≠ 0 := norm_pos_iff.1 (by rw [ht1]; exact one_pos)
    obtain ⟨k, hk⟩ := exists_nat_norm_sub_le ((s - t) / (t * (w - 1))) (by
      rw [norm_div, norm_mul, ht1, one_mul, div_le_one hdpos, hd]; exact ha)
    refine ⟨a + l ^ m * k, ?_⟩
    have h : s - u ^ (a + l ^ m * k) = t * (w - 1) * ((s - t) / (t * (w - 1)) - k)
        + -(t * (w ^ k - 1 - k * (w - 1))) := by
      rw [pow_add, pow_mul, ← hw, ← ht]
      field_simp
      ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_mul, ht1, one_mul, hd]
      calc _ ≤ (l : ℝ) ^ (-((j + m : ℕ) : ℤ)) * (l : ℝ) ^ (-1 : ℤ) := by gcongr
        _ = _ := by
          rw [← zpow_add₀ hl0.ne']; congr 1; push_cast; ring
    · rw [norm_neg, norm_mul, ht1, one_mul]
      refine (norm_pow_sub_lin_le w hw1.le k).trans ?_
      rw [hd, ← zpow_natCast, ← zpow_mul]
      apply zpow_le_zpow_right₀ hl1.le
      have := hj.1
      push_cast; omega
end GlobalTheory.Cyc

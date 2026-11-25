-- Prove2me | solution 1 for GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:53.098952+00:00
-- url     : https://prove2.me/submissions/44e6ad3b-0d7a-4b0f-aacd-9da24bc85b52

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_norm_add_of_lt
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_one_lt_l
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_norm_pow_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.LiftExp
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.Cyc.LiftExp
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), Lev l j → ∀ u : ℚ_[l],
    ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)) → ∀ k : ℤ, k ≠ 0 →
      ‖u ^ k - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValInt l k : ℤ))) := by
  intro l _ j hj u hu k hk
  have hu1 : ‖u‖ = 1 := by
    have h : ‖u - 1‖ < ‖(1 : ℚ_[l])‖ := by
      rw [hu, norm_one]
      exact zpow_lt_one_of_neg₀ one_lt_l (by have := hj.1; omega)
    have := norm_add_of_lt h
    simpa using this
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have key := norm_pow_nat j hj u hu k.natAbs (Int.natAbs_ne_zero.2 hk)
  unfold padicValInt
  rw [← key]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp
  · rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    have : (u ^ n)⁻¹ - 1 = -((u ^ n - 1) * (u ^ n)⁻¹) := by field_simp; ring
    rw [this, norm_neg, norm_mul, norm_inv, norm_pow, hu1]; simp
end GlobalTheory.Cyc.LiftExp

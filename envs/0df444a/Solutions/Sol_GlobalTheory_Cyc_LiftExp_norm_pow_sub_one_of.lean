-- Prove2me | solution 1 for GlobalTheory.Cyc.LiftExp.norm_pow_sub_one_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:59:30.782124+00:00
-- url     : https://prove2.me/submissions/13dcccf1-8fba-43e9-8f72-985d114c9cd3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_one_add_pow_expand
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_norm_add_of_lt
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_one_lt_l
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_zpow_lt

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
theorem _root_.solution (j : ℕ) (hj : 1 ≤ j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)))
    (n : ℕ) (e c : ℤ) (hn : ‖(n : ℚ_[l])‖ = (l : ℝ) ^ (-e))
    (hc : ‖((n.choose 2 : ℕ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-c)) (h1 : e < c + j) (h2 : e < 2 * j) :
    ‖u ^ n - 1‖ = (l : ℝ) ^ (-((j : ℤ) + e)) := by
  have hl0 : (l : ℝ) ≠ 0 := (zero_lt_one.trans one_lt_l).ne'
  have hx : ‖u - 1‖ ≤ 1 := by
    rw [hu]; exact zpow_le_one_of_nonpos₀ one_lt_l.le (by omega)
  obtain ⟨r, hr, h⟩ := one_add_pow_expand (u - 1) hx n
  rw [add_sub_cancel] at h
  have hm : ‖(n : ℚ_[l]) * (u - 1)‖ = (l : ℝ) ^ (-((j : ℤ) + e)) := by
    rw [norm_mul, hn, hu, ← zpow_add₀ hl0]; congr 1; ring
  rw [h, norm_add_of_lt, hm]
  rw [hm]
  refine (Padic.nonarchimedean _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul, norm_pow, hu]
    calc _ ≤ (l : ℝ) ^ (-c) * ((l : ℝ) ^ (-(j : ℤ))) ^ 2 := by gcongr
      _ = (l : ℝ) ^ (-c + (-(j : ℤ)) * 2) := by
        rw [zpow_add₀ hl0, zpow_mul]; norm_cast
      _ < _ := zpow_lt (by omega)
  · rw [norm_mul, norm_pow, hu]
    calc _ ≤ ((l : ℝ) ^ (-(j : ℤ))) ^ 3 * 1 := by gcongr
      _ = (l : ℝ) ^ ((-(j : ℤ)) * 3) := by
        rw [mul_one, zpow_mul]; norm_cast
      _ < _ := zpow_lt (by omega)
end GlobalTheory.Cyc.LiftExp

-- Prove2me | solution 1 for GlobalTheory.le_of_add_mul_choose_pred_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:37:09.400097+00:00
-- url     : https://prove2.me/submissions/2ef98332-2032-4182-87bc-ecd92f1e5f05

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BinomRatio
import Definitions.Def_ReciprocityTheory_SemistableReduction_FinrankRestrictTotalDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardExponentsAndChooseRatioBoundsPair
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sub_mul_choose_le_mul_choose


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (D T δ d ρ : ℕ) (hD : 2 ≤ D) (hT : 11 * D ^ 2 ≤ T)
    (hd : d ≤ δ * (T + 2 * D + 6).choose D) (hρ : ρ + δ * (T - 1).choose D ≤ d) :
    (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T := by
  have hT' : D * (2 * D + 7) ≤ T := by nlinarith
  have hTpos : (0 : ℝ) < T := by
    have : 0 < T := by nlinarith
    exact_mod_cast this
  have key := ReciprocityTheory.ChartRestriction.G.T0.sub_mul_choose_le_mul_choose T D hT' D le_rfl
  have hd' : (d : ℝ) ≤ δ * (((T + 2 * D + 6).choose D : ℕ) : ℝ) := by exact_mod_cast hd
  have hρ' : (ρ : ℝ) + δ * (((T - 1).choose D : ℕ) : ℝ) ≤ d := by exact_mod_cast hρ
  have hTD : (0 : ℝ) ≤ (T : ℝ) - D * (2 * D + 7) := by
    have : ((D : ℝ) * (2 * D + 7)) ≤ T := by exact_mod_cast hT'
    linarith
  have hδ : (0 : ℝ) ≤ δ := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have s1 := mul_le_mul_of_nonneg_left key hδ
  have s2 := mul_le_mul_of_nonneg_left hd' hTD
  have s3 := mul_le_mul_of_nonneg_left hρ' hTpos.le
  have s4 : (D : ℝ) * (2 * D + 7) * d ≤ 22 * (D : ℝ) ^ 2 * d :=
    mul_le_mul_of_nonneg_right (by nlinarith) hd0
  rw [le_div_iff₀ hTpos]
  nlinarith
end GlobalTheory

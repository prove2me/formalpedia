-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_1_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T13:07:24.394181+00:00
-- url     : https://prove2.me/submissions/07326284-a5fc-4566-a9aa-3f7f2755244d

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_exists_positive
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_one_sided_passage
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_exit_ratio
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_stopped_downward_split
import Theorems.Thm_Kyprianou_Ch08_StageB_source_technicalFullMomentExponentExistence_v2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

private theorem result81_lower_of_split
    {total lower upper restart Zx Za Wx Wa c : ℝ}
    (hWa : 0 < Wa) (hTotal : total = Zx - c * Wx)
    (hRestart : restart = Za - c * Wa) (hUpper : upper = Wx / Wa)
    (hSplit : total = lower + upper * restart) :
    lower = Zx - Za * Wx / Wa := by
  have hcancel : Wx / Wa * Wa = Wx := div_mul_cancel₀ Wx (ne_of_gt hWa)
  calc
    lower = (Zx - c * Wx) - (Wx / Wa) * (Za - c * Wa) := by
      rw [hTotal, hRestart, hUpper] at hSplit
      linarith only [hSplit]
    _ = Zx - Za * Wx / Wa + c * (Wx / Wa * Wa - Wx) := by ring
    _ = Zx - Za * Wx / Wa := by rw [hcancel, sub_self, mul_zero, add_zero]

private theorem result81_constant_for_downward_formula
    (ψ : ℝ → ℝ) (W down : ℝ → ℝ → ℝ)
    (positive : ∀ q x : ℝ, 0 < q →
      down q x = Zscale q (W q) x - q / Phi ψ q * W q x)
    (slope : ∀ x d : ℝ, HasPositiveFiniteRightPsiSlope ψ d →
      down 0 x = 1 - d * W 0 x)
    (other : (¬ ∃ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d) →
      ∀ x : ℝ, down 0 x = 1)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ c : ℝ, ∀ z : ℝ, down q z = Zscale q (W q) z - c * W q z := by
  rcases eq_or_lt_of_le hq with hzero | hpos
  · subst q
    by_cases hs : ∃ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d
    · obtain ⟨d, hd⟩ := hs
      exact ⟨d, fun z => by simpa [Zscale] using slope z d hd⟩
    · exact ⟨0, fun z => by simpa [Zscale] using other hs z⟩
  · exact ⟨q / Phi ψ q, fun z => positive q z hpos⟩

theorem solution : sourceCertificate_result8_1 := by
  intro Ω _ P _ D
  obtain ⟨ψ, hfull⟩ := source_technicalFullMomentExponentExistence_v2 Ω P D
  obtain ⟨W, hW, hpositive⟩ := source_result81_scale_exists_positive Ω P D ψ hfull.1
  obtain ⟨hdownPos, hdownZeroPos, hdownZeroElse⟩ :=
    source_result81_one_sided_passage Ω P D ψ hfull.1 W hW
  refine ⟨ψ, W, hfull.1, hW, hdownPos, hdownZeroPos, hdownZeroElse, ?_⟩
  intro q x a hq ha hxa
  have hWa := hpositive q a hq ha
  have hUpper := source_result81_upper_exit_ratio Ω P D ψ hfull.1 W hW q x a hq ha hxa
  obtain ⟨_, hc⟩ := result81_constant_for_downward_formula ψ W
    (downExpectation P D.X) hdownPos hdownZeroPos hdownZeroElse q hq
  exact ⟨hWa, hUpper, result81_lower_of_split hWa (hc x) (hc a)
    hUpper (source_result81_stopped_downward_split Ω P D q x a hq ha hxa)⟩

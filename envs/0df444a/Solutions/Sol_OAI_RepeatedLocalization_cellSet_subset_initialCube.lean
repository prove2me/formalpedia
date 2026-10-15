-- Prove2me | solution 1 for OAI.RepeatedLocalization.cellSet_subset_initialCube
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:07:08.450617+00:00
-- url     : https://prove2.me/submissions/5d8123ac-7d83-4d86-958a-45b5569b6696

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/Cells.lean:L47-L59
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.cellSet_subset_initialCube. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells

-- ---- from OAI.Probability.Localization.Cells ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

lemma cellSet_subset_initialCube {n : ℕ} (hn : 0 < n) (Q : Cell n) :
    cellSet Q ⊆ initialCube n := by
  intro z hz i hi
  have hd : 0 < Real.sqrt (n : ℝ) * (2 : ℝ)^Q.1 := by positivity
  have hidx : (Q.2 i : ℝ) + 1 ≤ (2 : ℝ)^Q.1 := by exact_mod_cast (Q.2 i).isLt
  have hl : 0 ≤ (Q.2 i : ℝ) / (Real.sqrt n * (2 : ℝ)^Q.1) := by positivity
  have hu : ((Q.2 i : ℝ) + 1) / (Real.sqrt n * (2 : ℝ)^Q.1) ≤ 1 / Real.sqrt n := by
    apply (div_le_iff₀ hd).mpr
    have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
    have he : 1 / Real.sqrt n * (Real.sqrt n * (2 : ℝ)^Q.1) = (2 : ℝ)^Q.1 := by field_simp
    rwa [he]
  have hw : -1 / (2 * Real.sqrt n) + 1 / Real.sqrt n = 1 / (2 * Real.sqrt n) := by ring
  exact ⟨(by linarith [(hz i).1]), (hz i).2.trans_le (by linarith)⟩

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (Q : Cell n) :
    cellSet Q ⊆ initialCube n := by
  first
    | exact OAI.RepeatedLocalization.cellSet_subset_initialCube hn Q
    | exact OAI.RepeatedLocalization.cellSet_subset_initialCube
    | (apply OAI.RepeatedLocalization.cellSet_subset_initialCube <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.cellSet_subset_initialCube <;> assumption)

-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.measurable_run
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:17:30.316196+00:00
-- url     : https://prove2.me/submissions/a75ee6a0-55b1-4ad6-8bee-53b2c6d25fb8

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/History.lean:L143-L157
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.measurable_run. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_measurable_attemptLetter

-- ---- from OAI.Probability.Localization.History ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma measurable_run {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) :
    Measurable (run P Q N) := by
  classical
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    have hf (h : Log n) : Measurable (fun z => if (state P Q h).stopped then h else
        h++[attemptLetter (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell z]) := by
      split
      · exact measurable_const
      · exact (measurable_of_countable (fun a : Letter n => h++[a])).comp (measurable_attemptLetter hn _ _)
    let f : Log n × Coordinate n → Log n := fun hz =>
      if (state P Q hz.1).stopped then hz.1 else hz.1++
        [attemptLetter (ProbabilityTheory.cond P (state P Q hz.1).event) (state P Q hz.1).cell hz.2]
    exact (measurable_from_prod_countable_right (f := f) hf).comp (ih.prodMk measurable_id)

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) :
    Measurable (run P Q N) := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.measurable_run hn P Q N
    | exact OAI.RepeatedLocalization.FiniteEntropy.measurable_run
    | (apply OAI.RepeatedLocalization.FiniteEntropy.measurable_run <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.measurable_run <;> assumption)

-- Prove2me | solution 1 for OAI.RandomKSAT.sum_fin_indicator_lt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:58:36.319062+00:00
-- url     : https://prove2.me/submissions/51e555e8-1dd8-4185-927c-441fb81750f7

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FiniteVariance.lean:L163-L178
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.sum_fin_indicator_lt. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance

-- ---- from OAI.Probability.SATVariance.FiniteVariance ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma sum_fin_indicator_lt {L N : ℕ} (hN : N ≤ L) :
    (∑ j : Fin L, if j.val < N then (1 : ℝ) else 0) = N := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < N then (1 : ℝ) else 0) L]
  calc
    (∑ j ∈ Finset.range L, if j < N then (1 : ℝ) else 0) =
        ∑ j ∈ Finset.range N, if j < N then (1 : ℝ) else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hN)
      intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [not_lt.mpr hj]
    _ = ∑ _j ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact ite_eq_left (Finset.mem_range.mp hj)
    _ = N := by simp

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.sum_fin_indicator_lt := @_root_.OAI.RandomKSAT.sum_fin_indicator_lt

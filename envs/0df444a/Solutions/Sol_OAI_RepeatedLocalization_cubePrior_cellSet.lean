-- Prove2me | solution 1 for OAI.RepeatedLocalization.cubePrior_cellSet
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:08:43.384218+00:00
-- url     : https://prove2.me/submissions/e53be053-47f1-4085-8cb9-86927b2f7358

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/Cells.lean:L61-L74
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.cubePrior_cellSet. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Theorems.Thm_OAI_RepeatedLocalization_cellSet_subset_initialCube

-- ---- from OAI.Probability.Localization.Experiment ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

lemma measurable_initialCube (n : ℕ) : MeasurableSet (initialCube n) := by
  apply MeasurableSet.univ_pi
  intro _
  exact measurableSet_Ico

lemma volume_initialCube (n : ℕ) :
    volume (initialCube n) = ENNReal.ofReal ((1 / Real.sqrt n) ^ n) := by
  unfold initialCube
  rw [Real.volume_pi_Ico]
  have hw : 1 / (2 * Real.sqrt n) - -1 / (2 * Real.sqrt n) = 1 / Real.sqrt n := by
    ring
  simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by positivity) n).symm

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.Cells ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

lemma cellSet_eq_pi {n : ℕ} (Q : Cell n) :
    cellSet Q = Set.pi univ (fun i => Ico (cellLower Q i) (cellLower Q i + cellWidth n Q.1)) := by
  ext z
  simp only [cellSet, mem_ofPred_eq, mem_pi, mem_univ, true_implies, mem_Ico]
  congr! 3
  simp only [cellLower, cellWidth]
  ring

lemma volume_cellSet {n : ℕ} (Q : Cell n) :
    volume (cellSet Q) = ENNReal.ofReal ((cellWidth n Q.1)^n) := by
  rw [cellSet_eq_pi, Real.volume_pi_Ico]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by unfold cellWidth; positivity) n).symm

lemma cubePrior_cellSet {n : ℕ} (hn : 0 < n) (Q : Cell n) :
    cubePrior n (cellSet Q) = ENNReal.ofReal ((1 / 2 : ℝ)^(n * Q.1)) := by
  unfold cubePrior
  rw [cond_apply (measurable_initialCube n), inter_eq_right.mpr (cellSet_subset_initialCube hn Q),
    volume_initialCube, volume_cellSet]
  have hp : 0 < (1 / Real.sqrt n)^n := by positivity
  rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_mul (inv_nonneg.mpr hp.le)]
  congr 1
  unfold cellWidth
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  simp only [one_div, inv_pow, inv_inv, mul_inv_rev ]
  rw [← mul_pow]
  have hc : Real.sqrt n * (((2 : ℝ)^Q.1)⁻¹ * (Real.sqrt n)⁻¹) = ((2 : ℝ)^Q.1)⁻¹ := by field_simp
  rw [hc, inv_pow, ← pow_mul, Nat.mul_comm Q.1 n]

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (Q : Cell n) :
    cubePrior n (cellSet Q) = ENNReal.ofReal ((1 / 2 : ℝ)^(n * Q.1)) := by
  first
    | exact OAI.RepeatedLocalization.cubePrior_cellSet hn Q
    | exact OAI.RepeatedLocalization.cubePrior_cellSet
    | (apply OAI.RepeatedLocalization.cubePrior_cellSet <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.cubePrior_cellSet <;> assumption)

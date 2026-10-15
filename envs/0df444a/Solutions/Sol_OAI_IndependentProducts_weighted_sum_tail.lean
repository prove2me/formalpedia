-- Prove2me | solution 1 for OAI.IndependentProducts.weighted_sum_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:11:40.294894+00:00
-- url     : https://prove2.me/submissions/d524f4cf-4462-4979-83f0-e0d6412f8a82

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/GaussianMoments.lean:L54-L74
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.weighted_sum_tail. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Theorems.Thm_OAI_IndependentProducts_second_moment_tail_bound

-- ---- from OAI.Analysis.ProductSpaces.GaussianMoments ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts
section WeightedMoments
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [Fintype ι]
variable {P : Measure Ω}

lemma weighted_sum_memLp_two [IsProbabilityMeasure P] (a : ι → ℝ) (U : ι → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 P) :
    MemLp (fun ω => ∑ i, a i ^ 2 * U i ω) 2 P := by
  exact memLp_finsetSum _ (fun i _ => (hU i).const_mul _)

variable [IsProbabilityMeasure P]

lemma weighted_sum_mean (a : ι → ℝ) (U : ι → Ω → ℝ) (hU : ∀ i, MemLp (U i) 2 P)
    (hm : ∀ i, ∫ ω, U i ω ∂P = 1) :
    (∫ ω, ∑ i, a i ^ 2 * U i ω ∂P) = ∑ i, a i ^ 2 := by
  rw [integral_finsetSum _ (fun i _ => ((hU i).integrable (by norm_num)).const_mul _)]
  simp_rw [integral_const_mul, hm, mul_one]

lemma weighted_sum_second_moment_le (a : ι → ℝ) (U : ι → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 P) (M : ℝ)
    (hm : ∀ i, (∫ ω, U i ω ^ 2 ∂P) ≤ M) :
    (∫ ω, (∑ i, a i ^ 2 * U i ω) ^ 2 ∂P) ≤ M * (∑ i, a i ^ 2) ^ 2 := by
  have hint : ∀ i, Integrable (fun ω => U i ω ^ 2) P :=
    fun i => (memLp_two_iff_integrable_sq (hU i).aestronglyMeasurable).mp (hU i)
  have hintV := (memLp_two_iff_integrable_sq (weighted_sum_memLp_two a U hU).aestronglyMeasurable).mp
    (weighted_sum_memLp_two a U hU)
  calc
    _ ≤ ∫ ω, (∑ i, a i ^ 2) * ∑ i, a i ^ 2 * U i ω ^ 2 ∂P := by
      apply integral_mono hintV
        ((integrable_finsetSum _ (fun i _ => (hint i).const_mul _)).const_mul _)
      intro ω
      have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun i => a i * U i ω)
      simpa only [mul_pow, ← mul_assoc, ← pow_two] using hc
    _ = (∑ i, a i ^ 2) * ∑ i, a i ^ 2 * ∫ ω, U i ω ^ 2 ∂P := by
      rw [integral_const_mul, integral_finsetSum]
      · simp_rw [integral_const_mul]
      · exact fun i _ => (hint i).const_mul _
    _ ≤ (∑ i, a i ^ 2) * ∑ i, a i ^ 2 * M := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hm i) (sq_nonneg _)
    _ = M * (∑ i, a i ^ 2) ^ 2 := by rw [← Finset.sum_mul]; ring

lemma weighted_sum_tail (a : ι → ℝ) (U : ι → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 P) (hmeas : ∀ i, Measurable (U i))
    (hpos : ∀ i ω, 0 ≤ U i ω) (hm : ∀ i, ∫ ω, U i ω ∂P = 1)
    (M : ℝ) (hM : 0 < M) (hm2 : ∀ i, (∫ ω, U i ω ^ 2 ∂P) ≤ M)
    (ha : 0 < ∑ i, a i ^ 2) :
    1 / (4 * M) ≤ P.real {ω | (∑ i, a i ^ 2) / 2 ≤ ∑ i, a i ^ 2 * U i ω} := by
  let S := ∑ i, a i ^ 2
  let V : Ω → ℝ := fun ω => ∑ i, a i ^ 2 * U i ω
  have hV := weighted_sum_memLp_two a U hU
  have hmV := weighted_sum_mean a U hU hm
  have htail := second_moment_tail_bound V hV (by fun_prop)
    (fun ω => Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (hpos i ω)))
    (S / 2) S (by dsimp [S]; positivity) (by dsimp [S]; linarith) hmV.ge
  have hm2V := weighted_sum_second_moment_le a U hU M hm2
  have hnonneg : 0 ≤ P.real {ω | S / 2 ≤ V ω} := measureReal_nonneg
  have hx : (S / 2) ^ 2 ≤ M * S ^ 2 * P.real {ω | S / 2 ≤ V ω} := by
    have hh := mul_le_mul_of_nonneg_right hm2V hnonneg
    nlinarith [htail]
  rw [div_le_iff₀ (by positivity : 0 < 4 * M)]
  have hs : 0 < S ^ 2 := sq_pos_of_pos ha
  nlinarith

end WeightedMoments
section GaussianVector
variable {ι : Type uι} [Fintype ι]

end GaussianVector
end IndependentProducts

namespace IndependentProducts

end IndependentProducts

namespace IndependentProducts

section GaussianFinite
variable {ι : Type uι} [Fintype ι]

end GaussianFinite
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [Fintype ι]
variable {P : Measure Ω}
variable [IsProbabilityMeasure P]

theorem solution (a : ι → ℝ) (U : ι → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 P) (hmeas : ∀ i, Measurable (U i))
    (hpos : ∀ i ω, 0 ≤ U i ω) (hm : ∀ i, ∫ ω, U i ω ∂P = 1)
    (M : ℝ) (hM : 0 < M) (hm2 : ∀ i, (∫ ω, U i ω ^ 2 ∂P) ≤ M)
    (ha : 0 < ∑ i, a i ^ 2) :
    1 / (4 * M) ≤ P.real {ω | (∑ i, a i ^ 2) / 2 ≤ ∑ i, a i ^ 2 * U i ω} := by
  first
    | exact OAI.IndependentProducts.weighted_sum_tail a U hU hmeas hpos hm M hM hm2 ha
    | exact OAI.IndependentProducts.weighted_sum_tail
    | (apply OAI.IndependentProducts.weighted_sum_tail <;> assumption)
    | (intros; apply OAI.IndependentProducts.weighted_sum_tail <;> assumption)

-- Prove2me | solution 2 for OAI.EntropyRateDimension.RandomGrid.exists_shift_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:47:12.665702+00:00
-- url     : https://prove2.me/submissions/247a20f1-5efc-41f9-9bda-2fc16f6c3d6b

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/GridCoupling.lean:L286-L315
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.RandomGrid.exists_shift_variation_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling

-- ---- from OAI.MeasureTheory.SelfSimilar.RandomGrid ----
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

end FiniteDistribution
namespace RandomGrid

attribute [local instance] OAI.EntropyRateDimension.RandomGrid.unitCircleProbability
theorem hit_eq_indicator (c : AddCircle (1 : ℝ)) (r : ℝ) :
    hit c r = (Metric.closedBall c r).indicator (fun _ => (1 : ℝ)) := by
  classical
  ext u
  change (if dist u c ≤ r then 1 else 0) = (if u ∈ Metric.closedBall c r then 1 else 0)
  rfl

theorem hit_integrable (c : AddCircle (1 : ℝ)) (r : ℝ) : Integrable (hit c r) := by
  rw [hit_eq_indicator]
  exact (integrable_const 1).indicator measurableSet_closedBall

theorem integral_hit (c : AddCircle (1 : ℝ)) {r : ℝ} (hr : 0 ≤ r) :
    (∫ u, hit c r u) = min 1 (2 * r) := by
  rw [hit_eq_indicator, integral_indicator_const _ measurableSet_closedBall]
  simp only [Measure.real, AddCircle.volume_closedBall, smul_eq_mul, mul_one]
  exact ENNReal.toReal_ofReal (le_min (by norm_num) (mul_nonneg (by norm_num) hr))

end RandomGrid

namespace MeasureEntropy

end MeasureEntropy

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.GridCoupling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace RandomGrid

attribute [local instance] unitCircleProbability
theorem exists_shift_cost_le {α : Type uα} (s : Finset α) (w : α → ℝ)
    (c : α → AddCircle (1 : ℝ)) (r : α → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hr : ∀ a ∈ s, 0 ≤ r a) :
    ∃ u : AddCircle (1 : ℝ),
      (∑ a ∈ s, w a * hit (c a) (r a) u) ≤ ∑ a ∈ s, w a * (2 * r a) := by
  have hi : ∀ a ∈ s, Integrable (fun u => w a * hit (c a) (r a) u) :=
    fun a _ => (hit_integrable (c a) (r a)).const_mul (w a)
  obtain ⟨u, hu⟩ := exists_le_integral (integrable_finsetSum s hi)
  refine ⟨u, hu.trans ?_⟩
  rw [integral_finsetSum s hi]
  apply Finset.sum_le_sum
  intro a ha
  rw [integral_const_mul, integral_hit (c a) (hr a ha)]
  exact mul_le_mul_of_nonneg_left (min_le_right _ _) (hw a ha)

theorem exists_shift_variation_bound {α : Type uα} (s : Finset α) (p : α → ℝ)
    (k : ℕ) (v m : α → Fin k → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hp : ∀ x ∈ s, 0 ≤ p x) :
    ∃ u : AddCircle (1 : ℝ),
      (∑ x ∈ s, p x * ∑ i, ∑ j,
        hit (-(m x j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m x i|/δ) u) ≤
      (8*k^2/δ)*(∑ x ∈ s, p x * ∑ i, |v x i-m x i|) := by
  classical
  let T : Finset (α × Fin k × Fin k) := s ×ˢ (Finset.univ ×ˢ Finset.univ)
  obtain ⟨u,hu⟩ := exists_shift_cost_le T (fun z => p z.1)
    (fun z => (-(m z.1 z.2.2/δ : ℝ) : AddCircle (1 : ℝ)))
    (fun z => 4*k*|v z.1 z.2.1-m z.1 z.2.1|/δ)
    (fun z hz => hp z.1 (Finset.mem_product.mp hz).1) (fun z _ => by positivity)
  refine ⟨u, ?_⟩
  have he : (∑ z ∈ T, p z.1 * hit (-(m z.1 z.2.2/δ : ℝ) : AddCircle (1 : ℝ))
      (4*k*|v z.1 z.2.1-m z.1 z.2.1|/δ) u) =
      ∑ x ∈ s, p x * ∑ i, ∑ j,
        hit (-(m x j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m x i|/δ) u := by
    simp only [T, Finset.sum_product, Finset.mul_sum]
  rw [he] at hu
  apply hu.trans_eq
  simp only [T, Finset.sum_product, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end RandomGrid

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.RandomGrid
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] unitCircleProbability


theorem solution.{uα} : type_of% @_root_.OAI.EntropyRateDimension.RandomGrid.exists_shift_variation_bound.{uα} := @_root_.OAI.EntropyRateDimension.RandomGrid.exists_shift_variation_bound.{uα}

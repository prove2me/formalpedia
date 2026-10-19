-- Prove2me | solution 1 for OAI.EntropyRateDimension.RandomGrid.exists_shift_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:46:45.808151+00:00
-- url     : https://prove2.me/submissions/e4901be0-0eb2-43d0-9f7a-de363c1e8c61

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.RandomGrid
universe uα
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] unitCircleProbability


theorem solution {α : Type uα} (s : Finset α) (p : α → ℝ)
    (k : ℕ) (v m : α → Fin k → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hp : ∀ x ∈ s, 0 ≤ p x) :
    ∃ u : AddCircle (1 : ℝ),
      (∑ x ∈ s, p x * ∑ i, ∑ j,
        hit (-(m x j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m x i|/δ) u) ≤
      (8*k^2/δ)*(∑ x ∈ s, p x * ∑ i, |v x i-m x i|) := by
  classical
  have hit_eq : ∀ c r, hit c r = (Metric.closedBall c r).indicator (fun _ => (1:ℝ)) := by
    intro c r; funext u; simp only [hit, Set.indicator, Metric.mem_closedBall]
  have hint : ∀ c r, Integrable (hit c r) := fun c r => by
    rw [hit_eq]; exact (integrable_const (1:ℝ)).indicator Metric.isClosed_closedBall.measurableSet
  have hI : ∀ c r, 0 ≤ r → ∫ u, hit c r u ≤ 2*r := by
    intro c r hr
    rw [hit_eq, integral_indicator_const _ Metric.isClosed_closedBall.measurableSet, smul_eq_mul,
      mul_one, Measure.real, AddCircle.volume_closedBall, ENNReal.toReal_ofReal (by positivity)]
    exact min_le_right _ _
  have hF : Integrable (fun u => ∑ x ∈ s, p x * ∑ i, ∑ j,
      hit (-(m x j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m x i|/δ) u) :=
    integrable_finset_sum _ fun x _ => (integrable_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => hint _ _).const_mul _
  obtain ⟨u, hu⟩ := exists_le_integral hF
  refine ⟨u, hu.trans ?_⟩
  rw [integral_finset_sum _ (fun x _ => (integrable_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => hint _ _).const_mul _), Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  have hpx := hp x hx
  rw [integral_const_mul, integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hint _ _)]
  calc p x * ∑ i, ∫ u, ∑ j, hit (-(m x j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m x i|/δ) u
      ≤ p x * ∑ i, ∑ j : Fin k, 2*(4*k*|v x i-m x i|/δ) := by
        gcongr with i
        rw [integral_finset_sum _ (fun j _ => hint _ _)]
        exact Finset.sum_le_sum fun j _ => hI _ _ (by positivity)
    _ = 8*k^2/δ * (p x * ∑ i, |v x i-m x i|) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
        ring


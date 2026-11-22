-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_uncapped_strict_isoB_ofReal_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T14:49:37.430331+00:00
-- url     : https://prove2.me/submissions/75c28b89-3e34-422c-afc6-6b583c164c4c

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Operations
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (lower upper : ℝ)
    (discount : ℝ≥0 → ℝ) (_hd : Measurable discount) (hdb : ∀ t, 0 ≤ discount t ∧ discount t ≤ 1)
    (reward : (ℝ≥0 → ℝ) → ℝ) (_hr : Measurable reward) (_hrb : ∀ f, 0 ≤ reward f ∧ reward f ≤ 1) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    let weightR := fun ω => if U ω < L ω then discount (U ω).toNNReal else 0
    let payoffR := fun ω => if U ω < L ω then discount (U ω).toNNReal * reward (fun s => X.X ((U ω).toNNReal + s) ω - X.X (U ω).toNNReal ω) else 0
    let rewR := fun ω => reward (fun s => X.X s ω)
    let discountE : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (discount t)
    let rewardE : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f => ENNReal.ofReal (reward f)
    (Integrable weightR P → Integrable payoffR P → Integrable rewR P →
     (∀ ω, 0 ≤ weightR ω) → (∀ ω, 0 ≤ payoffR ω) → (∀ ω, 0 ≤ rewR ω) →
     (ENNReal.ofReal (∫ ω, payoffR ω ∂P) = ∫⁻ ω, (if U ω < L ω then discountE ((U ω).toNNReal) * rewardE (fun t : ℝ≥0 => X.X ((U ω).toNNReal + t) ω - X.X ((U ω).toNNReal) ω) else 0) ∂P) ∧
     (ENNReal.ofReal (∫ ω, weightR ω ∂P) = ∫⁻ ω, (if U ω < L ω then discountE ((U ω).toNNReal) else 0) ∂P) ∧
     (ENNReal.ofReal (∫ ω, rewR ω ∂P) = ∫⁻ ω, rewardE (fun t : ℝ≥0 => X.X t ω) ∂P)) := by
  intro U L weightR payoffR rewR discountE rewardE hWeight hPayoff hRew hWeightNonneg
    hPayoffNonneg hRewNonneg
  refine ⟨?_, ?_, ?_⟩
  · rw [ofReal_integral_eq_lintegral_ofReal hPayoff (Filter.Eventually.of_forall hPayoffNonneg)]
    apply lintegral_congr
    intro ω
    by_cases hExit : U ω < L ω
    · have hDiscount : 0 ≤ discount (U ω).toNNReal := (hdb _).1
      simp [payoffR, discountE, rewardE, hExit, ENNReal.ofReal_mul hDiscount]
    · simp [payoffR, hExit]
  · rw [ofReal_integral_eq_lintegral_ofReal hWeight (Filter.Eventually.of_forall hWeightNonneg)]
    apply lintegral_congr
    intro ω
    by_cases hExit : U ω < L ω <;> simp [weightR, discountE, hExit]
  · exact ofReal_integral_eq_lintegral_ofReal hRew (Filter.Eventually.of_forall hRewNonneg)

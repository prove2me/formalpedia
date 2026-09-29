-- Prove2me | solution 1 for MarkovChainCLT.tvDist_comp_le_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T21:58:02.589669+00:00
-- url     : https://prove2.me/submissions/0457cb90-c9ce-4678-9f36-d6ed61058862

import Definitions.Def_TotalVariationDist
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Kernel.Composition.MeasureComp

open MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

/-- A uniform bound on `‖K(x,·) - ν‖` transfers to any initial distribution. -/
theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] (lam : Measure X) [IsProbabilityMeasure lam]
    (ν : Measure Y) [IsProbabilityMeasure ν] (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, tvDist (K x) ν ≤ C) :
    tvDist (K ∘ₘ lam) ν ≤ C := by
  refine Real.sSup_le ?_ hC0
  rintro r ⟨B, hB, rfl⟩
  -- the pointwise bound `|K(x,B) - ν B| ≤ ‖K(x,·) - ν‖ ≤ C`
  have hptw : ∀ x, |((K x) B).toReal - (ν B).toReal| ≤ C := by
    intro x
    have hb : BddAbove {r | ∃ A : Set Y, MeasurableSet A ∧
        r = |((K x) A).toReal - (ν A).toReal|} := by
      refine ⟨2, ?_⟩
      rintro s ⟨A, hA, rfl⟩
      have h1 : ((K x) A).toReal ≤ 1 :=
        ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
      have h2 : (ν A).toReal ≤ 1 :=
        ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
      rw [abs_le]
      constructor <;>
        [linarith [ENNReal.toReal_nonneg (a := (K x) A)];
         linarith [ENNReal.toReal_nonneg (a := ν A)]]
    have hin : |((K x) B).toReal - (ν B).toReal| ≤ tvDist (K x) ν :=
      le_csSup hb ⟨B, hB, rfl⟩
    exact le_trans hin (hC x)
  -- express the pushed-forward measure as an integral
  set g : X → ℝ := fun x => ((K x) B).toReal with hg
  have hgm : Measurable g := (Kernel.measurable_coe K hB).ennreal_toReal
  have hg0 : ∀ x, 0 ≤ g x := fun x => ENNReal.toReal_nonneg
  have hg1 : ∀ x, g x ≤ 1 := fun x =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hval : ((K ∘ₘ lam) B).toReal = ∫ x, g x ∂lam := by
    rw [Measure.bind_apply hB (Kernel.aemeasurable _)]
    refine (integral_toReal (Kernel.measurable_coe K hB).aemeasurable ?_).symm
    filter_upwards with x
    exact measure_lt_top _ _
  have hgint : Integrable g lam := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const (1:ℝ)).mono ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, abs_of_nonneg (hg0 x)]
    exact hg1 x
  -- average the pointwise bound
  have hconst : (ν B).toReal = ∫ _x, (ν B).toReal ∂lam := by
    rw [integral_const]
    simp [Measure.real]
  rw [hval]
  calc |(∫ x, g x ∂lam) - (ν B).toReal|
      = |∫ x, (g x - (ν B).toReal) ∂lam| := by
        rw [integral_sub hgint (integrable_const _), ← hconst]
    _ ≤ ∫ x, |g x - (ν B).toReal| ∂lam := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := lam) (f := fun x => g x - (ν B).toReal)
    _ ≤ ∫ _x, C ∂lam := by
        refine integral_mono ((hgint.sub (integrable_const _)).abs)
          (integrable_const C) (fun x => hptw x)
    _ = C := by rw [integral_const]; simp [Measure.real]

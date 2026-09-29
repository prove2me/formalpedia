-- Prove2me | solution 1 for MarkovChainCLT.tvDist_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T21:53:41.539883+00:00
-- url     : https://prove2.me/submissions/520b5a04-c7d1-488a-b76d-92f40e2f13b7

import Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_tvDist
import Mathlib.Probability.Kernel.Composition.MeasureComp

open MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

/-- **Data processing**: a Markov kernel cannot increase total variation distance. -/
theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist (K ∘ₘ μ) (K ∘ₘ ν) ≤ tvDist μ ν := by
  -- `tvDist μ ν ≥ 0`
  have hbdd : BddAbove {r | ∃ A : Set X, MeasurableSet A ∧ r = |(μ A).toReal - (ν A).toReal|} := by
    refine ⟨2, ?_⟩
    rintro r ⟨A, hA, rfl⟩
    have h1 : (μ A).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have h2 : (ν A).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    rw [abs_le]
    constructor <;>
      [linarith [ENNReal.toReal_nonneg (a := μ A)]; linarith [ENNReal.toReal_nonneg (a := ν A)]]
  have hnn : 0 ≤ tvDist μ ν :=
    le_csSup hbdd ⟨∅, MeasurableSet.empty, by simp⟩
  refine Real.sSup_le ?_ hnn
  rintro r ⟨B, hB, rfl⟩
  -- the pushed-forward measures evaluate as integrals of `x ↦ K x B`
  set g : X → ℝ := fun x => ((K x) B).toReal with hg
  have hgm : Measurable g := (Kernel.measurable_coe K hB).ennreal_toReal
  have hg0 : ∀ x, 0 ≤ g x := fun x => ENNReal.toReal_nonneg
  have hg1 : ∀ x, g x ≤ 1 := fun x =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hval : ∀ (ρ : Measure X), IsProbabilityMeasure ρ →
      ((K ∘ₘ ρ) B).toReal = ∫ x, g x ∂ρ := by
    intro ρ hρ
    haveI := hρ
    rw [Measure.bind_apply hB (Kernel.aemeasurable _)]
    refine (integral_toReal (Kernel.measurable_coe K hB).aemeasurable ?_).symm
    filter_upwards with x
    exact measure_lt_top _ _
  rw [hval μ inferInstance, hval ν inferInstance]
  exact MarkovChainCLT.abs_integral_sub_le_tvDist μ ν g hgm hg0 hg1

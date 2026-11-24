-- Prove2me | solution 1 for Kyprianou.Ch02.subordinatorMarginalNecessityV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:36:05.559571+00:00
-- url     : https://prove2.me/submissions/53d64e0c-3ee7-468c-a5ae-54f1a646878c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

import Theorems.Thm_Kyprianou_Ch02_levyMonotoneOfNonnegativeMarginalsV1
import Theorems.Thm_Kyprianou_Ch02_levyBoundedVariationNecessityV1
import Theorems.Thm_Kyprianou_Ch02_levyMonotoneForcesPositiveJumpSupportV1
import Theorems.Thm_Kyprianou_Ch02_levyMonotoneForcesNonnegativeBVDriftV1
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ X t ω) →
    levyMeasure (Set.Iio (0 : ℝ)) = 0 ∧
    σ = 0 ∧
    Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (levyMeasure.restrict (Set.Ioi (0 : ℝ))) ∧
    0 ≤ -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂levyMeasure := by
  intro hn
  have hm := Kyprianou.Ch02.levyMonotoneOfNonnegativeMarginalsV1 P X hX hn
  have hbv : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ := by
    filter_upwards [hm] with ω hω
    exact (hω.monotoneOn Set.univ).locallyBoundedVariationOn
  obtain ⟨hσ, hint⟩ := Kyprianou.Ch02.levyBoundedVariationNecessityV1
    a σ levyMeasure hlevyMeasure P X hX hchar hbv
  have hsupport := Kyprianou.Ch02.levyMonotoneForcesPositiveJumpSupportV1
    a σ levyMeasure hlevyMeasure P X hX hchar hm
  refine ⟨hsupport, hσ, hint.restrict, ?_⟩
  exact Kyprianou.Ch02.levyMonotoneForcesNonnegativeBVDriftV1
    a σ levyMeasure hlevyMeasure P X hX hchar hm hσ hint hsupport

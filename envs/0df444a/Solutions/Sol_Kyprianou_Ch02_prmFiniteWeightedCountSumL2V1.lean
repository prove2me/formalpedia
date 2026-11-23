-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteWeightedCountSumL2V1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:03:30.878285+00:00
-- url     : https://prove2.me/submissions/f8997d78-5fa5-4fc9-9143-e4ccbd25408e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmFiniteIntensityCountRealL2V1
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (F : Finset ι) (C : ι → Set (ℝ × ℝ))
    (hC : ∀ i ∈ F, MeasurableSet (C i))
    (hfinite : ∀ i ∈ F, LevyStochCalc.Poisson.referenceIntensity ν (C i) ≠ ⊤)
    (a : ι → ℝ) :
    MemLp (fun ω => ∑ i ∈ F, a i * (N.N ω (C i)).toReal) 2 P := by
  classical
  apply memLp_finset_sum F
  intro i hi
  exact (Kyprianou.Ch02.prmFiniteIntensityCountRealL2V1
    P ν N (C i) (hC i hi) (hfinite i hi)).const_mul (a i)

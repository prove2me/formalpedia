-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteMarkedIntegralSimpleApproxL2BoundV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:47:27.702906+00:00
-- url     : https://prove2.me/submissions/5cfe9f89-8e77-45ca-9da9-20978b3a6959
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_realMarkSimpleL2ApproxV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkedApproxL2BoundFromMarksV1
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B)) :
    ∀ t : ℝ≥0,
      ∃ (F : ℕ → Finset ℕ)
        (C : ℕ → ℕ → Set (ℝ × ℝ)) (a : ℕ → ℕ → ℝ),
        (∀ n i, i ∈ F n → MeasurableSet (C n i)) ∧
        (∀ n i, i ∈ F n →
          LevyStochCalc.Poisson.referenceIntensity ν (C n i) ≠ ⊤) ∧
        (∀ n i, i ∈ F n →
          C n i ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) ∧
        (∀ᵐ ω ∂P,
          Filter.Tendsto
            (fun n => ∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal)
            Filter.atTop
            (nhds (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
              z.2 ∂(N.N ω)))) ∧
        Filter.liminf
          (fun n => eLpNorm
            (fun ω => ∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal)
            2 P) Filter.atTop < ⊤ := by
  obtain ⟨f, hfpoint, hfL2⟩ :=
    Kyprianou.Ch02.realMarkSimpleL2ApproxV1 ν B hsecond
  exact Kyprianou.Ch02.prmFiniteMarkedApproxL2BoundFromMarksV1
    P ν N B hB hfinite hsecond f hfpoint hfL2

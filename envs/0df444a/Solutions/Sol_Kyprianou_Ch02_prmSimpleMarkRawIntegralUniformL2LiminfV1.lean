-- Prove2me | solution 1 for Kyprianou.Ch02.prmSimpleMarkRawIntegralUniformL2LiminfV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:22:15.29183+00:00
-- url     : https://prove2.me/submissions/2b5a0e46-8a71-4b75-9800-a669b5ee94c2

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkRawCampbellSecondMomentV1
import Theorems.Thm_Kyprianou_Ch02_prmCampbellIdentityImpliesUniformL2V1
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
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B))
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hfL2 : Filter.Tendsto
      (fun n => eLpNorm (fun x : ℝ => (f n) x - x) 2 (ν.restrict B))
      Filter.atTop (nhds 0))
    (hrawL2 : ∀ t : ℝ≥0, ∀ n,
      MemLp (fun ω =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          (f n) z.2 ∂(N.N ω)) 2 P) :
    ∀ t : ℝ≥0, Filter.liminf
      (fun n => eLpNorm
        (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          (f n) z.2 ∂(N.N ω)) 2 P)
      Filter.atTop < ⊤ := by
  apply Kyprianou.Ch02.prmCampbellIdentityImpliesUniformL2V1
    P ν N B hB hfinite hsecond f hfL2 hrawL2
  intro n t
  exact Kyprianou.Ch02.prmSimpleMarkRawCampbellSecondMomentV1
    P ν N B hB hfinite (f n) t

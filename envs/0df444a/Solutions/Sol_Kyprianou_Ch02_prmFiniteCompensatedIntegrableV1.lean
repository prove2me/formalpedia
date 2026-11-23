-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteCompensatedIntegrableV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:49:43.507798+00:00
-- url     : https://prove2.me/submissions/ffee1dc6-e974-4d87-96be-1659563c8d88
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionRawMarkedIntegralL1GivenFirstMomentV1
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
    (hfirst : Integrable (fun x : ℝ => x) (ν.restrict B))
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ) :
    ∀ t : ℝ≥0, Integrable ((fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) t) P := by
  intro t
  have hraw :
      Integrable (fun ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P :=
    Kyprianou.Ch02.prmFiniteRegionRawMarkedIntegralL1GivenFirstMomentV1
      P ν N B hB hfinite hfirst t
  have hconst : Integrable
      (fun _ : Ω => (t : ℝ) * (∫ x in B, x ∂ν)) P :=
    integrable_const _
  convert hraw.sub hconst using 1
  funext ω
  rfl

-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulCompensatedBandCharFunKLSV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:24:20.421643+00:00
-- url     : https://prove2.me/submissions/030d4a00-ea60-4334-b327-18af88f9f14f

import Theorems.Thm_Kyprianou_Ch02_realCharFunSubtractConstantCh02V1
import Theorems.Thm_Kyprianou_Ch02_finiteSmallBandCompensatedExponentAlgebraCh02V1
import Theorems.Thm_Kyprianou_finiteRegionPoissonIntegralCh02V3
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableAmbientV1
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (t : ℝ≥0) (ξ : ℝ) :
    charFun (P.map (Kyprianou.compensatedSmallJumpBand P levyMeasure N e t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in {x : ℝ | e ≤ |x| ∧ |x| < 1},
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure) := by
  let B : Set ℝ := {x : ℝ | e ≤ |x| ∧ |x| < 1}
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hfin : levyMeasure B < ⊤ :=
    lt_of_le_of_lt (measure_mono (fun _ hx => hx.1))
      (ProbabilityTheory.IsLevyMeasure.measure_setOf_abs_ge_lt_top hlevyMeasure he)
  let F : Ω → ℝ := fun ω =>
    ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)
  have hF : Measurable F :=
    Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1
      P levyMeasure N _ (measurableSet_Ioc.prod hB)
  have hraw := (Kyprianou.finiteRegionPoissonIntegralCh02V3
    P levyMeasure N B hB hfin).2 t ξ
  change charFun (P.map (fun ω => F ω - (t : ℝ) * ∫ x in B, x ∂levyMeasure)) ξ = _
  rw [Kyprianou.Ch02.realCharFunSubtractConstantCh02V1 P F hF.aemeasurable]
  change Complex.exp (((-((t : ℝ) * ∫ x in B, x ∂levyMeasure) * ξ : ℝ) : ℂ) *
    Complex.I) * charFun (P.map F) ξ = _
  rw [show charFun (P.map F) ξ = _ from hraw]
  exact Kyprianou.Ch02.finiteSmallBandCompensatedExponentAlgebraCh02V1
    levyMeasure B hB hfin (fun _ hx => hx.2) (t : ℝ) ξ

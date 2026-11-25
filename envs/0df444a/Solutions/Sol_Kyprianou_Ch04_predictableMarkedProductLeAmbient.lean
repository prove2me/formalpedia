-- Prove2me | solution 1 for Kyprianou.Ch04.predictableMarkedProductLeAmbient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:00:42.339943+00:00
-- url     : https://prove2.me/submissions/52189b6a-3b01-45f5-af9f-60748a4058b4

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_AvramDividend_Classical_ripple_predictable_le_ambient_product
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega)) :
    F.predictable.prod (inferInstance : MeasurableSpace Real) ≤
      (inferInstance : MeasurableSpace ((NNReal × Omega) × Real)) := by
  have hPred := AvramDividend.Classical.ripple_predictable_le_ambient_product F
  have hfst : @Measurable ((NNReal × Omega) × Real) (NNReal × Omega)
      inferInstance F.predictable Prod.fst :=
    fun S hS => (hPred S hS).preimage measurable_fst
  have hpair : @Measurable ((NNReal × Omega) × Real) ((NNReal × Omega) × Real)
      inferInstance (F.predictable.prod inferInstance) (fun z => (z.1, z.2)) :=
    hfst.prodMk measurable_snd
  intro S hS
  simpa using hpair hS

-- Prove2me | solution 1 for Kyprianou.Ch04.fixedHorizonSignedDrawdownInfimumLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T17:38:30.776942+00:00
-- url     : https://prove2.me/submissions/02a5f494-4385-4a6e-960e-77115bf1b0ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_Kyprianou_Ch04_fixedHorizonSignedExtremaMeasurable
import Theorems.Thm_Kyprianou_Ch04_fixedHorizonSignedExtremaStrictCDF
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_probability_real_law_ext_of_strict_CDF
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Identify the fixed-horizon laws using their strict lower-ray values. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (t : NNReal) (ht : 0 < t) :
    let A : Ω → ℝ := fun w => L.X t w - sSup ((fun s : NNReal => L.X s w) '' Iic t)
    let B : Ω → ℝ := fun w => sInf ((fun s : NNReal => L.X s w) '' Iic t)
    IdentDistrib A B P P := by
  intro A B
  letI : IsProbabilityMeasure P := L.isProbability
  obtain ⟨hA, hB⟩ := Kyprianou.Ch04.fixedHorizonSignedExtremaMeasurable P F L t
  letI : IsProbabilityMeasure (P.map A) :=
    Measure.isProbabilityMeasure_map hA.aemeasurable
  letI : IsProbabilityMeasure (P.map B) :=
    Measure.isProbabilityMeasure_map hB.aemeasurable
  refine ⟨hA.aemeasurable, hB.aemeasurable, ?_⟩
  apply avram_ws01e_b_probability_real_law_ext_of_strict_CDF
  intro a
  rw [Measure.map_apply hA measurableSet_Iio, Measure.map_apply hB measurableSet_Iio]
  exact Kyprianou.Ch04.fixedHorizonSignedExtremaStrictCDF P F L t ht a

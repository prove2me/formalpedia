-- Prove2me | solution 1 for Kyprianou.Ch04.fixedHorizonSignedExtremaStrictCDF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T17:44:35.443064+00:00
-- url     : https://prove2.me/submissions/a8766e17-05bb-4834-bc3d-60db3613dbab

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fixed_horizon_strict_reversal
import Theorems.Thm_Kyprianou_Ch04_signedDrawdownStrictThreshold
import Theorems.Thm_Kyprianou_Ch04_runningInfimumStrictThreshold
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (t : NNReal) (ht : 0 < t) (a : ℝ) :
    P {w : Ω | L.X t w - sSup ((fun s : NNReal => L.X s w) '' Iic t) < a} =
      P {w : Ω | sInf ((fun s : NNReal => L.X s w) '' Iic t) < a} := by
  have hA :
      {w : Ω | L.X t w - sSup ((fun s : NNReal => L.X s w) '' Iic t) < a} =
      {w : Ω | ∃ s : NNReal, s ≤ t ∧ L.X t w - L.X s w < a} := by
    ext w
    exact Kyprianou.Ch04.signedDrawdownStrictThreshold P F L t w a
  have hB :
      {w : Ω | sInf ((fun s : NNReal => L.X s w) '' Iic t) < a} =
      {w : Ω | ∃ s : NNReal, s ≤ t ∧ L.X s w - L.X 0 w < a} := by
    ext w
    exact Kyprianou.Ch04.runningInfimumStrictThreshold P F L t w a
  rw [hA, hB]
  exact avram_ws01e_b_fixed_horizon_strict_reversal L t ht a

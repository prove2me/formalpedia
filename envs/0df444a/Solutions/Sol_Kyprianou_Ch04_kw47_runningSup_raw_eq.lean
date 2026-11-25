-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_runningSup_raw_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T11:29:09.442321+00:00
-- url     : https://prove2.me/submissions/6259754f-d5ac-4a52-a0a2-52e03b94660f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F)
    (t : NNReal) (w : Omega) :
    runningSup L t w = sSup ((fun s : NNReal => L.X s w) '' Set.Iic t) := by 
  rw [(runningSup_eq_rawSup_nonneg L t w).1]
  change sSup (Set.range (fun r : Set.Icc (0 : NNReal) t => L.X r.1 w)) = _
  congr 1
  ext z
  simp only [Set.mem_range, Set.mem_image, Subtype.exists, Set.mem_Icc,
    Set.mem_Iic, zero_le, true_and, exists_prop]

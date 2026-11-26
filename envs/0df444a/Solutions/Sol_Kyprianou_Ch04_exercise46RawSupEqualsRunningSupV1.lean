-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RawSupEqualsRunningSupV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:48:47.933334+00:00
-- url     : https://prove2.me/submissions/1b156a98-9420-4115-ac7c-4141acec3813

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (w : Omega) (t : NNReal) :
    sSup ((fun u : NNReal => L.X u w) '' Iic t) = runningSup L t w := by
  rw [(runningSup_eq_rawSup_nonneg L t w).1]
  change sSup ((fun s : NNReal => L.X s w) '' Iic t) =
    sSup (Set.range fun s : Icc (0 : NNReal) t => L.X s.1 w)
  apply congrArg sSup
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, zero_le, hs⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, s.2.2, rfl⟩

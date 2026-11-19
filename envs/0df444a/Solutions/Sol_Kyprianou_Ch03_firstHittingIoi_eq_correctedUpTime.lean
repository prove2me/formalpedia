-- Prove2me | solution 1 for Kyprianou.Ch03.firstHittingIoi_eq_correctedUpTime
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:07:31.090938+00:00
-- url     : https://prove2.me/submissions/8e275f14-0d90-4d0f-9993-31189f27378e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : ℝ) (hx : 0 < x) (omega : Omega) :
    Kyprianou.Ch03.firstHittingTime L.X (Set.Ioi x) omega =
      AvramDividend.Classical.twoSidedExitUpTimeCorrected L x omega := by
  unfold Kyprianou.Ch03.firstHittingTime AvramDividend.Classical.twoSidedExitUpTimeCorrected
  have hset : {t : NNReal | 0 < t ∧ L.X t omega ∈ Set.Ioi x} = {t : NNReal | x < L.X t omega} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Ioi]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rcases eq_or_ne t 0 with rfl | ht
      · rw [L.X_zero] at h; linarith
      · exact pos_iff_ne_zero.mpr ht
  rw [hset, sInf_image]
  rfl

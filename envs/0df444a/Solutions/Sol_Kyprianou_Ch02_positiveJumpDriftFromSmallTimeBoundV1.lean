-- Prove2me | solution 1 for Kyprianou.Ch02.positiveJumpDriftFromSmallTimeBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:10:15.727897+00:00
-- url     : https://prove2.me/submissions/665a6067-e190-4628-851e-96a16fc3ab37

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_positiveLevyAnnulusIntegrableV1
import Theorems.Thm_Kyprianou_Ch02_positiveLevyAnnulusRestrictEqV1
import Theorems.Thm_Kyprianou_Ch02_positiveLevySmallMomentAnnulusSplitV1
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hs : T.levyMeasure (Set.Iio (0 : ℝ)) = 0)
    (r b : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsmall : Integrable (fun x : ℝ => x)
      (T.levyMeasure.restrict (Set.Ioo (0 : ℝ) r)))
    (hb : (∫ x in Set.Ioo (0 : ℝ) r, x ∂T.levyMeasure) ≤ b)
    (hd : T.drift = b + ∫ x in {x : ℝ | r ≤ |x| ∧ |x| < 1}, x ∂T.levyMeasure) :
    0 ≤ T.drift - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂T.levyMeasure := by
  have hi := Kyprianou.Ch02.positiveLevyAnnulusIntegrableV1
    T.levyMeasure T.levyMeasure_isLevyMeasure r hr
  have hs' := Kyprianou.Ch02.positiveLevyAnnulusRestrictEqV1 T.levyMeasure hs r
  have hsplit := Kyprianou.Ch02.positiveLevySmallMomentAnnulusSplitV1
    T.levyMeasure r hr hr1 hsmall hi
  change T.drift = b + ∫ x, x ∂T.levyMeasure.restrict
    {x : ℝ | r ≤ |x| ∧ |x| < 1} at hd
  rw [hs'] at hd
  rw [hd, hsplit]
  linarith

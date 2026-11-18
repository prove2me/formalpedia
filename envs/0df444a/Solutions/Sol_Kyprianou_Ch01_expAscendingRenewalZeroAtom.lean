-- Prove2me | solution 1 for Kyprianou.Ch01.expAscendingRenewalZeroAtom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:55:08.147492+00:00
-- url     : https://prove2.me/submissions/f25e4901-7458-471e-a4fe-e6b8f657848f

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_QueueingFundamentals_MG1_transforms
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem solution (mu : Measure ℝ) (x : ℝ) (hx : 0 ≤ x) :
    ((QueueingFundamentals.MG1.convPow mu 0)
      (Set.Icc (0 : ℝ) x)).toReal = 1 := by
  simp [QueueingFundamentals.MG1.convPow, hx]

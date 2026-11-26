-- Prove2me | solution 1 for Kyprianou.Ch05.renewalJointKernelTailENN
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:23:51.753559+00:00
-- url     : https://prove2.me/submissions/dc4a736a-dcab-47ab-9e9a-ba5e5f1a4ec6

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Theorems.Thm_Kyprianou_Ch05_renewalTailKernelInner
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Integrate the pointwise inner-kernel identity. -/
theorem solution
    (V F : Measure Real) (x u y : Real) (hu : 0 < u) :
    renewalJointKernel V F x (Ioi u) (Ioi y) =
      ∫⁻ v in Icc (0 : Real) x, (if y < x-v then F (Ioi (x-v+u)) else 0) ∂V := by
  classical
  unfold renewalJointKernel
  apply lintegral_congr
  intro v
  convert renewalTailKernelInner F v x u y hu using 1
  congr 1

-- Prove2me | solution 1 for Kyprianou.Ch05.smithZeroDelayRenewalIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:58:08.425584+00:00
-- url     : https://prove2.me/submissions/8378dd3f-e22e-42c7-a8b2-87f3a23fa96a

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Smith's renewal measure with zero initial delay is exactly the Chapter 5 renewal measure, including the zeroth convolution power. -/
theorem solution
    (F : Measure Real) [IsProbabilityMeasure F] :
    SmithRegenerative.Equilibrium.renewalMeasure (Measure.dirac 0) F =
      renewalMeasure F := by
  have hp (n : Nat) : renewalConvolutionPower F n =
      QueueingFundamentals.MG1.convPow F n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (renewalConvolutionPower F n).conv F =
        (QueueingFundamentals.MG1.convPow F n).conv F
      rw [ih]
  have hprob (n : Nat) : IsProbabilityMeasure (QueueingFundamentals.MG1.convPow F n) := by
    induction n with
    | zero => change IsProbabilityMeasure (Measure.dirac (0 : Real)); infer_instance
    | succ n ih =>
      letI := ih
      change IsProbabilityMeasure ((QueueingFundamentals.MG1.convPow F n).conv F)
      infer_instance
  unfold SmithRegenerative.Equilibrium.renewalMeasure renewalMeasure
  congr 1
  funext n
  letI := hprob n
  rw [hp n]
  simp [Measure.dirac_conv]

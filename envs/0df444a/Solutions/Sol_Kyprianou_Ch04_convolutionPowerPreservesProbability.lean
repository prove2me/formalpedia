-- Prove2me | solution 1 for Kyprianou.Ch04.convolutionPowerPreservesProbability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:57:39.315511+00:00
-- url     : https://prove2.me/submissions/2608d26b-01e3-486a-a348-7079c0889ed6

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
open MeasureTheory
set_option autoImplicit false
/-- Every finite convolution power of a probability measure is a probability measure. -/
theorem solution
    (eta : Measure ℝ) [IsProbabilityMeasure eta] :
    ∀ n : ℕ, IsProbabilityMeasure
      (Nat.rec (motive := fun _ => Measure ℝ) (Measure.dirac (0 : ℝ))
        (fun _ mu => mu.conv eta) n) := by
  intro n
  induction n with
  | zero =>
      simpa using (inferInstance :
        IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  | succ n ih =>
      change IsProbabilityMeasure
        ((Nat.rec (motive := fun _ => Measure ℝ) (Measure.dirac (0 : ℝ))
          (fun _ mu => mu.conv eta) n).conv eta)
      letI : IsProbabilityMeasure
          (Nat.rec (motive := fun _ => Measure ℝ) (Measure.dirac (0 : ℝ))
            (fun _ mu => mu.conv eta) n) := ih
      exact Measure.probabilitymeasure_of_probabilitymeasures_conv _ _

-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_power_has_weighted_support
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T18:17:03.688241+00:00
-- url     : https://prove2.me/submissions/702fa4ac-c286-45dd-9f4e-f55b69c305a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_center_ideal_power_has_weighted_support_core

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (v : Fin (m + 1) → Real)
    (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : Real) * v 0)
    (R : Real) (he : ∀ i, R ≤ (e i : Real) * v i)
    (n : Nat) (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : P ∈ FormalInterpolation.logarithmicCenterIdeal c T e ^ n)
    (b : Fin (m + 1) → Nat)
    (hcoeff : MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (FormalInterpolation.formalJet c P) ≠ 0) :
    (n : Real) * R ≤ ∑ i, (b i : Real) * v i := by
  exact OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_power_has_weighted_support_core
    c T e v hv hT R he n P hP b hcoeff

-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.formalJet_has_nonnegative_weighted_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:46:59.524976+00:00
-- url     : https://prove2.me/submissions/e796f2b3-3a3e-4274-a369-e56464b80870

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution {m : Nat} (c : Fin m -> Complex) (T : Fin m -> Nat)
    (v : Fin (m + 1) -> Real)
    (hv : forall i, 0 <= v i)
    (hT : forall i, v i.succ <= (T i : Real) * v 0)
    (P : MvPolynomial (Fin (m + 1)) Complex) :
    FormalInterpolation.hasWeightedSupport v 0
      (FormalInterpolation.formalJet c P) := by
  intro b hb
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (Nat.cast_nonneg _) (hv i)
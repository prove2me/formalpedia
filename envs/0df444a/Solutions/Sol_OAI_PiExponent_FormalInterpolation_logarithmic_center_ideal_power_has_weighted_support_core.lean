-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_power_has_weighted_support_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T18:33:48.076869+00:00
-- url     : https://prove2.me/submissions/229370cc-b1f0-498e-bea6-db80a64a30a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_logarithmic_center_generator_has_weighted_support
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_ideal_power_has_weighted_support_of_generators

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {m : Nat} (c : Fin m -> Complex) (T : Fin m -> Nat)
    (e : Fin (m + 1) -> Nat) (v : Fin (m + 1) -> Real)
    (hv : forall i, 0 <= v i)
    (hT : forall i, v i.succ <= (T i : Real) * v 0)
    (R : Real) (he : forall i, R <= (e i : Real) * v i)
    (n : Nat) (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : Membership.mem (FormalInterpolation.logarithmicCenterIdeal c T e ^ n) P) :
    FormalInterpolation.hasWeightedSupport v ((n : Real) * R)
      (FormalInterpolation.formalJet c P) := by
  refine FormalInterpolation.ideal_power_has_weighted_support_of_generators
    v R n (FormalInterpolation.formalJet c)
    (fun i => FormalInterpolation.logarithmicCoordinate c T i ^ e i) ?_ P ?_
  · intro i
    exact FormalInterpolation.formalJet_logarithmic_center_generator_has_weighted_support
      c T e v hv hT R he i
  · simpa [FormalInterpolation.logarithmicCenterIdeal] using hP

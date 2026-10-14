-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.formalJet_logarithmic_center_generator_has_weighted_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T06:17:23.5875+00:00
-- url     : https://prove2.me/submissions/dd52e578-e52e-4d7b-b7cf-42ad9bc35709

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_WeightedSupport
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCoordinate_formalJet_has_weighted_support
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_pow

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {m : Nat} (c : Fin m -> Complex) (T : Fin m -> Nat)
    (e : Fin (m + 1) -> Nat) (v : Fin (m + 1) -> Real)
    (hv : forall i, 0 <= v i)
    (hT : forall i, v i.succ <= (T i : Real) * v 0)
    (R : Real) (he : forall i, R <= (e i : Real) * v i)
    (i : Fin (m + 1)) :
    FormalInterpolation.hasWeightedSupport v R
      (FormalInterpolation.formalJet c
        (FormalInterpolation.logarithmicCoordinate c T i ^ e i)) := by
  have hcoord :=
    OAI.PiExponent.FormalInterpolation.logarithmicCoordinate_formalJet_has_weighted_support
      c T v hv hT i
  have hpow :=
    OAI.PiExponent.FormalInterpolation.hasWeightedSupport_pow
      v (v i) hv (FormalInterpolation.formalJet c
        (FormalInterpolation.logarithmicCoordinate c T i)) hcoord (e i)
  have hmap :
      FormalInterpolation.formalJet c
        (FormalInterpolation.logarithmicCoordinate c T i ^ e i) =
      (FormalInterpolation.formalJet c
        (FormalInterpolation.logarithmicCoordinate c T i)) ^ e i := by
    exact map_pow (FormalInterpolation.formalJet c)
      (FormalInterpolation.logarithmicCoordinate c T i) (e i)
  rw [hmap]
  intro b hb
  have h := hpow b hb
  have he' : R <= (e i : Real) * v i := he i
  exact le_trans he' h

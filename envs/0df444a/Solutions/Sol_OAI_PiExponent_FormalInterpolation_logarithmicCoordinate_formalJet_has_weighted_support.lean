-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCoordinate_formalJet_has_weighted_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T06:27:32.533826+00:00
-- url     : https://prove2.me/submissions/27a4700f-45e7-4585-8f18-ebed3ad74ac1

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_WeightedSupport
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCoordinate_formalJet_coeff_support_profile

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    {m : Nat} (c : Fin m -> Complex) (T : Fin m -> Nat)
    (v : Fin (m + 1) -> Real)
    (hv : forall i, 0 <= v i)
    (hT : forall i, v i.succ <= (T i : Real) * v 0)
    (i : Fin (m + 1)) :
    FormalInterpolation.hasWeightedSupport v (v i)
      (FormalInterpolation.formalJet c
        (FormalInterpolation.logarithmicCoordinate c T i)) := by
  intro b hb
  have hp :=
    OAI.PiExponent.FormalInterpolation.logarithmicCoordinate_formalJet_coeff_support_profile
      c T i b hb
  rcases hp with hzero | hcases | htail
  · rw [hzero.2]
    simp [hzero.1]
  · obtain ⟨k, hik, hunit⟩ := hcases
    rw [hunit]
    simp [hik]
  · obtain ⟨k, n, hik, htail, hkn⟩ := htail
    have hcast : (T k : Real) <= (n : Real) := by exact_mod_cast hkn
    have hbound : v i <= (n : Real) * v 0 := by
      calc
        v i = v k.succ := by rw [hik]
        _ <= (T k : Real) * v 0 := hT k
        _ <= (n : Real) * v 0 := mul_le_mul_of_nonneg_right hcast (hv 0)
    rw [htail]
    simpa using hbound

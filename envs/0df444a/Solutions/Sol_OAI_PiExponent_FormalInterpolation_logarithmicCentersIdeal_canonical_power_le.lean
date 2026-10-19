-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_canonical_power_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:40:45.827352+00:00
-- url     : https://prove2.me/submissions/63c987f5-c7ba-4eb9-bd78-a14bbf1b8781

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeal_canonical_power_le
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_ideal_finset_prod_pow_le

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (he : ∀ i, 0 < e i)
    (hcut : ∀ i, e 0 ≤ T i * e i.succ) (n : Nat) :
    (logarithmicCentersIdeal c (fun _ => e 0) e) ^ (n + m) ≤
      (logarithmicCentersIdeal c T e) ^ n := by
  classical
  simpa only [logarithmicCentersIdeal, Finset.prod_pow] using
    OAI.PiExponent.FormalInterpolation.ideal_finset_prod_pow_le
      (fun j => logarithmicCenterIdeal (c j) (fun _ => e 0) e)
      (fun j => logarithmicCenterIdeal (c j) T e)
      (n + m) n
      (fun j =>
        OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_canonical_power_le
          (c j) T e he hcut n)
-- Prove2me | solution 1 for GlobalTheory.DivPowLPrime.factorial_mul_qCoef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:04:40.414443+00:00
-- url     : https://prove2.me/submissions/7f7c2aff-971a-4abd-b2b1-119bb1cb5433

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedPowersPrimeUnique
import Theorems.Thm_GlobalTheory_DivPowLPrime_lPrime_eq_pow
import Theorems.Thm_GlobalTheory_DivPowLPrime_factorial_eq
import Theorems.Thm_GlobalTheory_DivPowLPrime_isUnit_factPrimePart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DivPowLPrime
variable {O : Type} [CommRing O] [IsLocalRing O] {l : ℕ}
namespace GlobalTheory.DivPowLPrime
theorem _root_.solution (hl : l.Prime) (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O) (m : ℕ)
    (hv : padicValNat l m.factorial ≤ lPrimeExp l * m) :
    (m.factorial : O) * qCoef O l m = (lPrime l : O) ^ m := by
  have hu := isUnit_factPrimePart hl hlO m
  have hf : (m.factorial : O) = (l : O) ^ padicValNat l m.factorial * (factPrimePart l m : O) := by
    have h := congrArg (Nat.cast : ℕ → O) (factorial_eq hl m)
    rwa [Nat.cast_mul, Nat.cast_pow] at h
  rw [hf, qCoef, qExp, lPrime_eq_pow, Nat.cast_pow, ← pow_mul]
  calc (l : O) ^ padicValNat l m.factorial * (factPrimePart l m : O) *
        ((l : O) ^ (lPrimeExp l * m - padicValNat l m.factorial) * Ring.inverse (factPrimePart l m : O))
      = (l : O) ^ (padicValNat l m.factorial + (lPrimeExp l * m - padicValNat l m.factorial)) *
          ((factPrimePart l m : O) * Ring.inverse (factPrimePart l m : O)) := by rw [pow_add]; ring
    _ = _ := by rw [Ring.mul_inverse_cancel _ hu, Nat.add_sub_cancel' hv, mul_one]
end GlobalTheory.DivPowLPrime

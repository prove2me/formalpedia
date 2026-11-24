-- Prove2me | solution 1 for GlobalTheory.DivPowLPrime.qCoef_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:56.100707+00:00
-- url     : https://prove2.me/submissions/a0f1ebbc-02ba-4c4a-8511-64fa6e83cc2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedPowersPrimeUnique
import Theorems.Thm_GlobalTheory_DivPowLPrime_lPrime_eq_pow

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
theorem _root_.solution {m : ℕ} (h : lPrimeExp l ≤ qExp l m) :
    qCoef O l m = (lPrime l : O) * ((l : O) ^ (qExp l m - lPrimeExp l) * Ring.inverse (factPrimePart l m : O)) := by
  rw [qCoef, lPrime_eq_pow, Nat.cast_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]
end GlobalTheory.DivPowLPrime

-- Prove2me | solution 1 for GlobalTheory.DivPowLPrime.isUnit_factPrimePart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:42:40.246885+00:00
-- url     : https://prove2.me/submissions/b7e2c454-edb4-4b17-9861-aeb6aa5653ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedPowersPrimeUnique
import Theorems.Thm_GlobalTheory_DivPowLPrime_isUnit_natCast_of_coprime

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
theorem _root_.solution (hl : l.Prime) (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O) (m : ℕ) :
    IsUnit (factPrimePart l m : O) :=
  isUnit_natCast_of_coprime hlO (Nat.coprime_ordCompl hl (Nat.factorial_ne_zero m))
end GlobalTheory.DivPowLPrime

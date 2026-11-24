-- Prove2me | solution 1 for GlobalTheory.TorsionFreeDividedPowers.ofFactorialUnits_dpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:39:05.603231+00:00
-- url     : https://prove2.me/submissions/60e82ba4-a93d-401d-85be-3b3151ccb118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowersPrime

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
open GlobalTheory GlobalTheory.TorsionFreeDividedPowers
open DividedPowers
namespace GlobalTheory.TorsionFreeDividedPowers
theorem _root_.solution {A : Type} [CommRing A] (h : ∀ n : ℕ, IsUnit (n.factorial : A))
    (J : Ideal A) {n : ℕ} {x : A} (hx : x ∈ J) :
    (ofFactorialUnits h J).dpow n x = Ring.inverse (n.factorial : A) * x ^ n :=
  OfInvertibleFactorial.dpow_eq_of_mem hx
end GlobalTheory.TorsionFreeDividedPowers

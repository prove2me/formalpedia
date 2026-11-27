-- Prove2me | solution 1 for GlobalTheory.tensorProduct_mk_one_injective_of_isTorsionFree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:42:37.884927+00:00
-- url     : https://prove2.me/submissions/66222a7f-5bc8-4be7-a3bd-65bd1a364f7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
open TensorProduct
namespace GlobalTheory
theorem _root_.solution {S : Type*} [CommRing S] [IsDomain S]
    (F : Type*) [Field F] [Algebra S F] [FaithfulSMul S F] (M : Type*) [AddCommGroup M]
    [Module S M] [Module.IsTorsionFree S M] :
    Function.Injective (TensorProduct.mk S F M 1) := by
  letI : Algebra (FractionRing S) F := FractionRing.liftAlgebra S F
  have h1 : Function.Injective (TensorProduct.mk S (FractionRing S) M 1) := by
    rw [IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors S)]
    intro c
    exact IsSMulRegular.of_ne_zero (nonZeroDivisors.coe_ne_zero c)
  have h2 := Module.FaithfullyFlat.tensorProduct_mk_injective
    (A := FractionRing S) (B := F) (FractionRing S ⊗[S] M)
  have h3 := (AlgebraTensorModule.cancelBaseChange S (FractionRing S) F F M).injective.comp
    (h2.comp h1)
  intro a b hab
  apply h3
  simpa using hab
end GlobalTheory

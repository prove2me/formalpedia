-- Prove2me | solution 1 for GlobalTheory.inK_injective_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:00:06.107161+00:00
-- url     : https://prove2.me/submissions/4263d33a-29dd-4e4b-aaed-3284dd60517a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodValuationBound
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] :
    Function.Injective (inK K H : H →ₗ[O] K ⊗[O] H) := by
  have h1 : Function.Injective ((Algebra.linearMap O K).rTensor H) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective O K)
  intro x y hxy
  apply (TensorProduct.lid O H).symm.injective
  apply h1
  simpa [inK] using hxy
end GlobalTheory

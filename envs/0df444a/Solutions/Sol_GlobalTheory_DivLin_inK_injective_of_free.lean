-- Prove2me | solution 1 for GlobalTheory.DivLin.inK_injective_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:16.100709+00:00
-- url     : https://prove2.me/submissions/4a7e9709-4b96-465e-92a6-50797196b198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
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
open GlobalTheory GlobalTheory.DivLin
namespace GlobalTheory.DivLin
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] :
    Function.Injective (inK (O := O) K H) := by
  have hf : Function.Injective (Algebra.linearMap O K) := IsFractionRing.injective O K
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := H) (Algebra.linearMap O K) hf
  have e : (inK K H : H →ₗ[O] K ⊗[O] H) =
      ((Algebra.linearMap O K).rTensor H) ∘ₗ (TensorProduct.lid O H).symm.toLinearMap := by
    ext h; simp [inK]
  rw [e]
  exact h2.comp (TensorProduct.lid O H).symm.injective
end GlobalTheory.DivLin

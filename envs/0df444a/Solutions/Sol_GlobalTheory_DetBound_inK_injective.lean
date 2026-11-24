-- Prove2me | solution 1 for GlobalTheory.DetBound.inK_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:10:58.501383+00:00
-- url     : https://prove2.me/submissions/6d374d01-128c-443f-8316-8c512a48e701

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegral
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
noncomputable section
open GlobalTheory GlobalTheory.DetBound
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
namespace GlobalTheory.DetBound
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] : Function.Injective (inK K H (O := O)) := by
  have h : (inK K H (O := O)) = ((Algebra.linearMap O K).rTensor H) ∘ₗ (TensorProduct.lid O H).symm.toLinearMap := by
    ext h; simp [inK]
  rw [h, LinearMap.coe_comp]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective O K)).comp
    (TensorProduct.lid O H).symm.injective
end GlobalTheory.DetBound

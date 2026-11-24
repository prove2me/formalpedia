-- Prove2me | solution 1 for GlobalTheory.includeRight_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:43.830444+00:00
-- url     : https://prove2.me/submissions/0dc25767-8e64-470b-bcb7-b0e3436b2f80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_ringHom_faithfullyFlat_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
namespace GlobalTheory
theorem _root_.solution (k K B : Type*) [CommRing k] [CommRing K] [CommRing B]
    [Algebra k K] [Algebra k B] [Module.FaithfullyFlat k K] :
    ((Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) : B →+* K ⊗[k] B).FaithfullyFlat := by
  have h := ringHom_faithfullyFlat_comp (f := algebraMap B (B ⊗[k] K))
    (g := (Algebra.TensorProduct.comm k B K : B ⊗[k] K →+* K ⊗[k] B))
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
    (.of_bijective (Algebra.TensorProduct.comm k B K).bijective)
  exact h
end GlobalTheory

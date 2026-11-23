-- Prove2me | solution 1 for GlobalTheory.LocalFlat.range_lTensor_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:11.324919+00:00
-- url     : https://prove2.me/submissions/ce51cc17-ead6-470e-a2f4-644baec0e883

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal

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
open GlobalTheory.LocalFlat
variable {A : Type u} [CommRing A]
variable {M : Type w} [AddCommGroup M] [Module A M]
namespace GlobalTheory.LocalFlat
theorem _root_.solution {F G : Type*} [AddCommGroup F] [Module A F] [AddCommGroup G] [Module A G]
    (h : G →ₗ[A] F) (N : Submodule A F) (hN : ∀ g, h g ∈ N) :
    range (h.lTensor M) ≤ range (N.subtype.lTensor M) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨(h.codRestrict N hN).lTensor M y, ?_⟩
  rw [← lTensor_comp_apply]
  rfl
end GlobalTheory.LocalFlat

-- Prove2me | solution 1 for GlobalTheory.QCoh.topologicalKrullDim_eq_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:33.77078+00:00
-- url     : https://prove2.me/submissions/e450c1c6-c709-43e8-818f-a6a4b8287e5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution {T : Type*} [TopologicalSpace T] :
    topologicalKrullDim T = ⊥ ↔ IsEmpty T := by
  rw [topologicalKrullDim, Order.krullDim_eq_bot_iff]
  exact ⟨fun h ↦ ⟨fun x ↦ h.false ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩,
    fun h ↦ ⟨fun Z ↦ h.false Z.isIrreducible.nonempty.some⟩⟩
end GlobalTheory.QCoh

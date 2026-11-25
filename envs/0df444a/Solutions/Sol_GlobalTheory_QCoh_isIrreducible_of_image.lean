-- Prove2me | solution 1 for GlobalTheory.QCoh.isIrreducible_of_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:06:09.821799+00:00
-- url     : https://prove2.me/submissions/44b25088-0197-4ede-b8ff-1bb38b0e9b1f

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
theorem _root_.solution {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] {f : S → T}
    (hf : Topology.IsInducing f) {s : Set S} (h : IsIrreducible (f '' s)) : IsIrreducible s := by
  refine ⟨h.nonempty.of_image, fun a b ha hb ⟨x, hx, hxa⟩ ⟨y, hy, hyb⟩ ↦ ?_⟩
  obtain ⟨a, ha', rfl⟩ := hf.isOpen_iff.1 ha
  obtain ⟨b, hb', rfl⟩ := hf.isOpen_iff.1 hb
  obtain ⟨_, ⟨z, hz, rfl⟩, hza⟩ := h.2 a b ha' hb' ⟨_, ⟨x, hx, rfl⟩, hxa⟩ ⟨_, ⟨y, hy, rfl⟩, hyb⟩
  exact ⟨z, hz, hza⟩
end GlobalTheory.QCoh

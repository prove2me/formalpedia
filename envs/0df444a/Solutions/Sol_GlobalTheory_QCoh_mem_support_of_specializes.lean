-- Prove2me | solution 1 for GlobalTheory.QCoh.mem_support_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:07:43.777627+00:00
-- url     : https://prove2.me/submissions/c11ebff2-72c4-478e-8d12-19b6dde50310

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_mem_support_iff_primeIdealOf
import Theorems.Thm_GlobalTheory_QCoh_mem_primeCompl_primeIdealOf_iff


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
theorem _root_.solution [F.IsQuasicoherent] {x y : X} (h : x ⤳ y)
    (hx : x ∈ support F) : y ∈ support F := by
  obtain ⟨U, hU, hy⟩ := exists_affine_mem y
  have hxU : x ∈ U := h.mem_open U.2 hy
  refine (mem_support_iff_primeIdealOf hU ⟨y, hy⟩).2 (Module.mem_support_mono ?_
    ((mem_support_iff_primeIdealOf hU ⟨x, hxU⟩).1 hx))
  intro f hf
  by_contra hf'
  exact (mem_primeCompl_primeIdealOf_iff hU ⟨x, hxU⟩ f).2 (h.mem_open (X.basicOpen f).2
    ((mem_primeCompl_primeIdealOf_iff hU ⟨y, hy⟩ f).1 hf')) hf
end GlobalTheory.QCoh

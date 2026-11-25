-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsRegular.isAdmissible_iff_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:07.989574+00:00
-- url     : https://prove2.me/submissions/5eef7db5-d41d-4aca-9111-86ddfd6cdd3d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Theorems.Thm_GroundTheory_PAdicHodge_IsRegular_comparison_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
open GroundTheory.PAdicHodge.IsRegular
variable {G F B : Type*} [Group G] [Field F] [CommRing B] [IsDomain B] [Algebra F B]
  [MulSemiringAction G B] [SMulCommClass G F B] (h : IsRegular G F B)
include h
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
namespace GroundTheory.PAdicHodge.IsRegular
theorem _root_.solution [FiniteDimensional F V] :
    IsAdmissible B ρ ↔ Function.Bijective (comparison B ρ) := by
  letI := h.field
  haveI := h.free ρ
  haveI := h.finite ρ
  refine ⟨fun hadm => ⟨h.comparison_injective ρ, h.comparison_surjective ρ hadm⟩, fun hbij => ?_⟩
  have := (LinearEquiv.ofBijective (comparison B ρ) hbij).finrank_eq
  rwa [Module.finrank_baseChange, Module.finrank_baseChange] at this
end GroundTheory.PAdicHodge.IsRegular

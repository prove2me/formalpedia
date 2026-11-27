-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsRegular.isAdmissible_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:38.947916+00:00
-- url     : https://prove2.me/submissions/3aee723f-6a11-46a8-8b2d-f48fd0acfec9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Theorems.Thm_GroundTheory_PAdicHodge_IsRegular_finrank_le

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
theorem _root_.solution [FiniteDimensional F V] {ι : Type*} [Fintype ι]
    {x : ι → DB B ρ} (hx : LinearIndependent B (fun i => (x i : B ⊗[F] V)))
    (hcard : finrank F V ≤ Fintype.card ι) : IsAdmissible B ρ := by
  letI := h.field
  haveI := h.free ρ
  haveI := h.finite ρ
  have hE : LinearIndependent (invariantRing G F B) x :=
    LinearIndependent.of_comp (DB B ρ).subtype (hx.restrict_scalars' (invariantRing G F B))
  exact le_antisymm (h.finrank_le ρ) (hcard.trans hE.fintype_card_le_finrank)
end GroundTheory.PAdicHodge.IsRegular

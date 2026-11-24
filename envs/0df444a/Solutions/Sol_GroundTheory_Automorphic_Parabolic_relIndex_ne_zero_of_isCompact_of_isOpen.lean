-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.relIndex_ne_zero_of_isCompact_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:42:35.409055+00:00
-- url     : https://prove2.me/submissions/34272f95-89b9-42f4-96c8-27086a830096

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {K L : Subgroup G} (hK : IsCompact (K : Set G))
    (hL : IsOpen (L : Set G)) : L.relIndex K ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hopen : IsOpen ((L.subgroupOf K : Subgroup K) : Set K) := hL.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen (L.subgroupOf K) hopen
  exact Subgroup.index_ne_zero_of_finite
end GroundTheory.Automorphic.Parabolic

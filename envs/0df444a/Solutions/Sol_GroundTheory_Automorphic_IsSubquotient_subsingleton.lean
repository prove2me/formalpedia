-- Prove2me | solution 1 for GroundTheory.Automorphic.IsSubquotient.subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:00:29.280449+00:00
-- url     : https://prove2.me/submissions/ddd199f1-23e2-4963-8c5c-64b2566a6b1a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthSubquotient

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
open Function Parabolic
universe u
variable {G : Type*} [Group G] {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup U] [Module ℂ U]
variable {π : Representation ℂ G W} {ρ : Representation ℂ G V} {θ : Representation ℂ G U}
namespace GroundTheory.Automorphic
namespace IsSubquotient
theorem _root_.solution [Subsingleton V] (h : IsSubquotient π ρ) : Subsingleton W := by
  obtain ⟨C, p, hp⟩ := h
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := hp a
  obtain ⟨y, rfl⟩ := hp b
  rw [Subsingleton.elim x y]
end IsSubquotient
end GroundTheory.Automorphic

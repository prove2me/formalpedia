-- Prove2me | solution 1 for GroundTheory.Automorphic.isSmooth_subrep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:51.434001+00:00
-- url     : https://prove2.me/submissions/2ee67fc5-b3a6-4e2e-9fee-b521497b504d

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
variable {G : Type*} [Group G] [TopologicalSpace G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
variable [IsTopologicalGroup G]
namespace GroundTheory.Automorphic
theorem _root_.solution (hρ : IsSmooth ρ) (C : Subrepresentation ρ) :
    IsSmooth C.toRepresentation := by
  intro y
  refine Subgroup.isOpen_mono (fun g hg => ?_) (hρ (y : V))
  rw [mem_stabilizerOf] at hg ⊢
  exact Subtype.ext hg
end GroundTheory.Automorphic

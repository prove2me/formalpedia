-- Prove2me | solution 1 for GroundTheory.Automorphic.isSmooth_indRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:57.205516+00:00
-- url     : https://prove2.me/submissions/86879490-96fb-4302-820c-cc7ad6992b38

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_Induction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G)
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W)
variable [IsTopologicalGroup G]
namespace GroundTheory.Automorphic
theorem _root_.solution : IsSmooth (indRep H σ) := by
  intro f
  obtain ⟨-, K, hK, hfK⟩ := f.2
  refine Subgroup.isOpen_mono (fun k hk => ?_) hK
  rw [mem_stabilizerOf]
  exact Subtype.ext (funext fun x => hfK k hk x)
end GroundTheory.Automorphic

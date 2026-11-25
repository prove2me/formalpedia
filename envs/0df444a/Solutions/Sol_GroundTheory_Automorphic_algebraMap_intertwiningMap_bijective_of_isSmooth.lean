-- Prove2me | solution 1 for GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:23.750471+00:00
-- url     : https://prove2.me/submissions/6a518a0f-20a6-4d83-85a3-9965f0407888

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Theorems.Thm_GroundTheory_Automorphic_algebraMap_intertwiningMap_bijective_of_rank_le_aleph0
import Theorems.Thm_GroundTheory_Automorphic_rank_le_aleph0_of_isSmooth

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
open Polynomial Cardinal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace.SeparableSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic
theorem _root_.solution (hρ : IsSmooth ρ) [ρ.IsIrreducible] :
    Function.Bijective (algebraMap ℂ (Representation.IntertwiningMap ρ ρ)) :=
  algebraMap_intertwiningMap_bijective_of_rank_le_aleph0 (rank_le_aleph0_of_isSmooth hρ)
end GroundTheory.Automorphic

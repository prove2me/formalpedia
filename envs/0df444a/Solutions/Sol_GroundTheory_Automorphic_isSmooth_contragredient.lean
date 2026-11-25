-- Prove2me | solution 1 for GroundTheory.Automorphic.isSmooth_contragredient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:24.83495+00:00
-- url     : https://prove2.me/submissions/b31eb33b-5df8-423c-921d-89d420bd32f5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_smoothPart


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
open Set Filter Topology
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.Automorphic
theorem _root_.solution : IsSmooth (contragredient ρ) :=
  isSmooth_smoothPart _
end GroundTheory.Automorphic

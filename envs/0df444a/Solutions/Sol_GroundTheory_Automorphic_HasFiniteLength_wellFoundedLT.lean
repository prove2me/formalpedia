-- Prove2me | solution 1 for GroundTheory.Automorphic.HasFiniteLength.wellFoundedLT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:29.015798+00:00
-- url     : https://prove2.me/submissions/a6b2cf03-df05-4da8-9dff-ca6676cedcf2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Theorems.Thm_GroundTheory_Automorphic_hasFiniteLength_iff

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
open Function
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic
namespace HasFiniteLength
theorem _root_.solution (h : HasFiniteLength ρ) :
    WellFoundedLT (Subrepresentation ρ) :=
  (hasFiniteLength_iff.1 h).1
end HasFiniteLength
end GroundTheory.Automorphic

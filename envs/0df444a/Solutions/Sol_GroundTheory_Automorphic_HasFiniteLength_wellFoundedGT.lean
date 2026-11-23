-- Prove2me | solution 1 for GroundTheory.Automorphic.HasFiniteLength.wellFoundedGT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:29.057459+00:00
-- url     : https://prove2.me/submissions/de07185a-dbe1-4b95-993a-7ab5c66f684c

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
    WellFoundedGT (Subrepresentation ρ) :=
  (hasFiniteLength_iff.1 h).2
end HasFiniteLength
end GroundTheory.Automorphic

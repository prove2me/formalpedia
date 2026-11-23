-- Prove2me | solution 1 for GroundTheory.Automorphic.hasFiniteLength_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:21.407692+00:00
-- url     : https://prove2.me/submissions/01e908a1-f119-492d-b09b-47dbd829105a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice

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
theorem _root_.solution [Subsingleton V] : HasFiniteLength ρ := by
  have : Subsingleton ρ.asModule := inferInstanceAs (Subsingleton V)
  exact IsFiniteLength.of_subsingleton
end GroundTheory.Automorphic

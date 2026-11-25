-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mul_e_sub_mem_vermaIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:21:43.810999+00:00
-- url     : https://prove2.me/submissions/cf621a28-d189-4461-be55-e64df8fbeb03

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (lam : Fin n → ℂ) (u : U n) (k : Fin n) :
    u * (e (k, k) - algebraMap ℂ (U n) (lam k)) ∈ vermaIdeal lam :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨u, k, rfl⟩)
end GroundTheory.Automorphic.HarishChandra

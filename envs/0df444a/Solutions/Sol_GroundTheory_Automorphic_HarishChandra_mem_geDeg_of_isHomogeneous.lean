-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mem_geDeg_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:44.583284+00:00
-- url     : https://prove2.me/submissions/52048ca9-f5ad-421c-9cf5-76a025081427

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero

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
theorem _root_.solution {f : Poly n} {d : ℕ} (hf : f.IsHomogeneous d) :
    f ∈ geDeg d := by
  intro s hs
  by_contra h
  have h2 : s.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hf h
  omega
end GroundTheory.Automorphic.HarishChandra

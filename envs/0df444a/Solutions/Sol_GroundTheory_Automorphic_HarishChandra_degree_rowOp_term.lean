-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.degree_rowOp_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:49.328248+00:00
-- url     : https://prove2.me/submissions/786208de-94e1-45c2-9250-819d906946de

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_degree_sub_single

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
theorem _root_.solution {i j k : Fin n} {s : Fin n × Fin n →₀ ℕ} (hs : s (j, k) ≠ 0) :
    (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1)).degree = s.degree := by
  rw [map_add, Finsupp.degree_single, ← degree_sub_single hs]
  ring
end GroundTheory.Automorphic.HarishChandra

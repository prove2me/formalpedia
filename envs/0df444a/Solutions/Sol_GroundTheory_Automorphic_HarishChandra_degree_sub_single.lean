-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.degree_sub_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:05.843527+00:00
-- url     : https://prove2.me/submissions/313f28c2-ab0b-4e0b-aec6-33a022521b43

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
theorem _root_.solution {s : Fin n × Fin n →₀ ℕ} {a : Fin n × Fin n} (h : s a ≠ 0) :
    (s - Finsupp.single a 1).degree + 1 = s.degree := by
  have hle : Finsupp.single a 1 ≤ s := by
    rw [Finsupp.single_le_iff]; omega
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, Finsupp.degree_single]
end GroundTheory.Automorphic.HarishChandra

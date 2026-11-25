-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.isUpper_of_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:11:40.991029+00:00
-- url     : https://prove2.me/submissions/76b030b2-dd53-4ebb-bf8d-6cf4c3df87c1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular

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
open scoped IsMulCommutative
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {P : Fin n × Fin n → Prop} {m : Fin n × Fin n →₀ ℕ}
    (hm : ∀ a ∈ m.support, P a) {a : Fin n × Fin n} (ha : ¬ P a) : m a = 0 := by
  by_contra h
  exact ha (hm a (Finsupp.mem_support_iff.2 h))
end GroundTheory.Automorphic.HarishChandra

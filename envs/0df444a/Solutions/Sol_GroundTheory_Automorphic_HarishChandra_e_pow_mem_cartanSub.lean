-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.e_pow_mem_cartanSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:59.797956+00:00
-- url     : https://prove2.me/submissions/4cc36488-691e-4f4b-9354-74cff16def9c

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
theorem _root_.solution (i : Fin n) (k : ℕ) : e (n := n) (i, i) ^ k ∈ cartanSub n :=
  Subalgebra.pow_mem _ (Algebra.subset_adjoin (s := cartanSet n) (Set.mem_range_self i)) k
end GroundTheory.Automorphic.HarishChandra

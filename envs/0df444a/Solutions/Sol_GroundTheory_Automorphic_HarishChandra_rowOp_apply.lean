-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rowOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:43.288165+00:00
-- url     : https://prove2.me/submissions/6a0075d2-a336-48f2-85fb-65c22816ad62

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (i j : Fin n) (f : Poly n) :
    rowOp i j f = ∑ k : Fin n, MvPolynomial.X (i, k) * MvPolynomial.pderiv (j, k) f := by
  simp [rowOp, LinearMap.sum_apply]
end GroundTheory.Automorphic.HarishChandra

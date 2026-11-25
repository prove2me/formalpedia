-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rowOp_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:50:42.824801+00:00
-- url     : https://prove2.me/submissions/5f885b03-c68d-4b21-aa35-1f235cc1d026

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_apply


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
theorem _root_.solution (i j : Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ) :
    rowOp i j (monomial s c) =
      ∑ k, monomial (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1)) (c * s (j, k)) := by
  rw [rowOp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_monomial, X, monomial_mul, one_mul]
end GroundTheory.Automorphic.HarishChandra

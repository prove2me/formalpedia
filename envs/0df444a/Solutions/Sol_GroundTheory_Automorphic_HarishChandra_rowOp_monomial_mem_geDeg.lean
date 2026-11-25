-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rowOp_monomial_mem_geDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:57.479799+00:00
-- url     : https://prove2.me/submissions/8df1dbc2-ca79-4c5a-8777-4dfeb2a11e84

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_monomial_mem_geDeg
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_monomial
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_monomial_term_mem
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_degree_rowOp_term

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
theorem _root_.solution {t : ℕ} (i j : Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ)
    (h : t ≤ s.degree) : rowOp i j (monomial s c) ∈ geDeg t := by
  rw [rowOp_monomial]
  refine Submodule.sum_mem _ fun k _ => rowOp_monomial_term_mem c _ fun hs => ?_
  apply monomial_mem_geDeg
  rw [degree_rowOp_term hs]; exact h
end GroundTheory.Automorphic.HarishChandra

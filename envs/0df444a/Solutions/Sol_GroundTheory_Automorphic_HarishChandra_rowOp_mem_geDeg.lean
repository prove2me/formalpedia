-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rowOp_mem_geDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:12.591978+00:00
-- url     : https://prove2.me/submissions/df2312cd-a894-46d6-988a-9c09380d8317

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_map_mem_of_monomial
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_monomial_mem_geDeg

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
theorem _root_.solution {t : ℕ} (i j : Fin n) {f : Poly n} (hf : f ∈ geDeg t) :
    rowOp i j f ∈ geDeg t := by
  refine map_mem_of_monomial (rowOp i j) _ (fun s => t ≤ s.degree) (fun s hs => ?_)
    (fun s c hs => rowOp_monomial_mem_geDeg i j s c hs)
  by_contra hlt
  exact hs (hf s (not_le.1 hlt))
end GroundTheory.Automorphic.HarishChandra

-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.hmt_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:29.201025+00:00
-- url     : https://prove2.me/submissions/183a0b4e-efa6-4eb1-a603-260ee39f77c5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_single_mem_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_mem_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_mem_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cone_mem_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ordIn_subset_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_rho_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory
universe w
variable {ι : Type w}
variable [LinearOrder ι]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution : ∀ (n : ℕ) (i : Fin (n + 1) → ι),
    hmt n i ∈ Finsupp.supported ℤ ℤ (rangeIn (Set.range i))
  | 0, _ => Submodule.zero_mem _
  | n + 1, i => by
    refine cone_mem_rangeIn (Set.mem_range_self 0) (Submodule.sub_mem _ (Submodule.sub_mem _
      (single_mem_rangeIn i 1) (Finsupp.supported_mono (ordIn_subset_rangeIn _) (rho_mem _ i))) ?_)
    exact lin_mem_rangeIn _ (fun j _ => solution n j) (bd_mem_rangeIn (single_mem_rangeIn i 1))
end GroundTheory.Arith.SchemeCoh

-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.bd_mem_rangeIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:15.509949+00:00
-- url     : https://prove2.me/submissions/a144336e-c94e-4428-a1c3-9621524ad885

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_map_mem_supported
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_rangeIn

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
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {n : ℕ} {S : Set ι} {c : Chain ι (n + 1)}
    (hc : c ∈ Finsupp.supported ℤ ℤ (rangeIn S)) :
    bd n c ∈ Finsupp.supported ℤ ℤ (rangeIn S) :=
  map_mem_supported _ (fun j hj z => by
    rw [bd_single]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Finsupp.single_mem_supported ℤ z
        (mem_rangeIn.2 ((Set.range_comp_subset_range _ _).trans (mem_rangeIn.1 hj))))) hc
end GroundTheory.Arith.SchemeCoh

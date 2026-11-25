-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.rho_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:04.815144+00:00
-- url     : https://prove2.me/submissions/44d20bc5-de45-4c9c-be6c-805f32809d8f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_map_mem_supported
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_single_mem_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_mem_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_ordIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_strictMono_of_fin_one
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ocone_mem_ordIn

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
    rho n i ∈ Finsupp.supported ℤ ℤ (ordIn (Set.range i))
  | 0, i => Finsupp.single_mem_supported ℤ _ (mem_ordIn.2 ⟨strictMono_of_fin_one _, subset_rfl⟩)
  | n + 1, i => by
    refine ocone_mem_ordIn i ?_
    refine map_mem_supported _ (fun j hj z => ?_) (bd_mem_rangeIn (single_mem_rangeIn i 1))
    rw [lin_single]
    exact Submodule.smul_mem _ z (Finsupp.supported_mono
      (fun k hk => mem_ordIn.2 ⟨(mem_ordIn.1 hk).1, (mem_ordIn.1 hk).2.trans (mem_rangeIn.1 hj)⟩)
      (solution n j))
end GroundTheory.Arith.SchemeCoh

-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.rho_of_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:13:37.592506+00:00
-- url     : https://prove2.me/submissions/8fa88ff7-b10e-4419-a68c-1fb32a11bb03

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_ordFrom
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ocone_single_of_not_lt
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_ocone_add_ocone_bd
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_minIdx_of_strictMono

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
theorem _root_.solution : ∀ (n : ℕ) (i : Fin (n + 1) → ι), StrictMono i →
    rho n i = Finsupp.single i 1
  | 0, _, _ => rfl
  | n + 1, i, hi => by
    have h1 : lin (rho n) (bd n (Finsupp.single i 1)) = bd n (Finsupp.single i 1) := by
      rw [bd_single, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, lin_single, one_smul,
        solution n _ (hi.comp (Fin.strictMono_succAbove k))]
    change ocone (minIdx i) (lin (rho n) (bd n (Finsupp.single i 1))) = _
    rw [h1, minIdx_of_strictMono hi]
    have key := bd_ocone_add_ocone_bd n (i 0) (c := Finsupp.single i 1)
      (Finsupp.single_mem_supported ℤ _ (mem_ordFrom.2 ⟨hi, le_rfl⟩))
    rw [ocone_single_of_not_lt (lt_irrefl _), map_zero, zero_add] at key
    exact key
end GroundTheory.Arith.SchemeCoh

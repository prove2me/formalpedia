-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.bd_cone_add_cone_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:12.856113+00:00
-- url     : https://prove2.me/submissions/f4217cdd-67b0-4988-9685-f2b134d984ec

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cone_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cons_comp_succAbove_succ
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cons_comp_succAbove_zero


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
theorem _root_.solution (n : ℕ) (s : ι) (c : Chain ι (n + 1)) :
    bd (n + 1) (cone s c) + cone s (bd n c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add]
    rw [add_add_add_comm, hf, hg]
  | single i z =>
    rw [cone_single, bd_single, Fin.sum_univ_succ, bd_single, map_sum]
    simp only [Fin.val_zero, pow_zero, one_smul, cons_comp_succAbove_zero,
      cons_comp_succAbove_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, map_zsmul,
      cone_single]
    rw [add_assoc, ← Finset.sum_add_distrib]
    simp
end GroundTheory.Arith.SchemeCoh

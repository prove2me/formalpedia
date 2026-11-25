-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.aug_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:09.403065+00:00
-- url     : https://prove2.me/submissions/cf451f8b-ad7c-471e-aa76-0a3f6f0f7084

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_aug_single

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
theorem _root_.solution (c : Chain ι 1) : aug (bd 0 c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | single i z =>
    rw [bd_single, Fin.sum_univ_two]
    simp [aug_single]
end GroundTheory.Arith.SchemeCoh

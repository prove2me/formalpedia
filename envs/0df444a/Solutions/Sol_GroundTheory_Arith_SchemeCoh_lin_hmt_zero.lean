-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.lin_hmt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:09.13263+00:00
-- url     : https://prove2.me/submissions/5e5a4849-795f-4a2f-8e37-0c48bd2659a2

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_single

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
theorem _root_.solution (c : Chain ι 0) : lin (hmt (ι := ι) 0) c = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, hf, hg, add_zero]
  | single i z => rw [lin_single, hmt, smul_zero]
end GroundTheory.Arith.SchemeCoh

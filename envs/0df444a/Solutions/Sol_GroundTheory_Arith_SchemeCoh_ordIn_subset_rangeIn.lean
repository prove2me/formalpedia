-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ordIn_subset_rangeIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:56.085669+00:00
-- url     : https://prove2.me/submissions/6bd17f18-4936-4d34-82a1-b03e8babab5f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_ordIn

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
theorem _root_.solution {n : ℕ} (S : Set ι) : ordIn (n := n) S ⊆ rangeIn S :=
  fun _ h => mem_rangeIn.2 (mem_ordIn.1 h).2
end GroundTheory.Arith.SchemeCoh

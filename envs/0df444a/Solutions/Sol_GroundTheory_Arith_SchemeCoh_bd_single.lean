-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.bd_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:53:37.025281+00:00
-- url     : https://prove2.me/submissions/1544c1ea-299c-47e6-b349-aa0b5ff63480

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_chainMap_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_apply

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
theorem _root_.solution (n : ℕ) (i : Fin (n + 2) → ι) (z : ℤ) :
    bd n (Finsupp.single i z) =
      ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) • Finsupp.single (i ∘ k.succAbove) z := by
  rw [bd_apply]
  simp only [chainMap_single]
end GroundTheory.Arith.SchemeCoh

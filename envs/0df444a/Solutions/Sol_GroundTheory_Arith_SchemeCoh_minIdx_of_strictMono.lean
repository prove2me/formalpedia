-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.minIdx_of_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:11.078456+00:00
-- url     : https://prove2.me/submissions/54c521fb-e575-4188-81c7-1d008845d535

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_minIdx_le

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
theorem _root_.solution {n : ℕ} {i : Fin (n + 1) → ι} (hi : StrictMono i) : minIdx i = i 0 :=
  le_antisymm (minIdx_le i 0)
    (Finset.le_inf' _ _ fun a _ => hi.monotone (Fin.zero_le a))
end GroundTheory.Arith.SchemeCoh

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cyclCoord_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:14.713552+00:00
-- url     : https://prove2.me/submissions/de521f10-11b7-4370-9de0-d772271d3f24

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {k : ℕ} {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1)))
    (y : PadicAlgCl p) : cyclCoord k η y 0 = normTrace (cycl p k) y := by
  rw [cyclCoord, Nat.sub_zero, hη.pow_eq_one, mul_one]
end GroundTheory.PAdicHodge

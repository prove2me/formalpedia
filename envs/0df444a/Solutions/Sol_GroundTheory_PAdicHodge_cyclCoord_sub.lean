-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cyclCoord_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:13.826282+00:00
-- url     : https://prove2.me/submissions/92f69a8a-a9ee-4ecb-931b-64da42583467

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_sub


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
theorem _root_.solution (k : ℕ) (η y y' : PadicAlgCl p) (i : ℕ) :
    cyclCoord k η (y - y') i = cyclCoord k η y i - cyclCoord k η y' i := by
  rw [cyclCoord, cyclCoord, cyclCoord, sub_mul, normTrace_sub]
end GroundTheory.PAdicHodge

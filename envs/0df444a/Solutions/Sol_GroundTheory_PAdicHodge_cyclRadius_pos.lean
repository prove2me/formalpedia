-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cyclRadius_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:04:10.708597+00:00
-- url     : https://prove2.me/submissions/86272423-7737-4d90-a115-aebfcdc9ad88

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_inv_p_le_cyclRadius

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
theorem _root_.solution (k : ℕ) : 0 < cyclRadius p (k + 1) :=
  lt_of_lt_of_le (inv_pos.2 (by exact_mod_cast (Fact.out : p.Prime).pos)) (inv_p_le_cyclRadius k)
end GroundTheory.PAdicHodge

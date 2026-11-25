-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cyclRadius_succ_pow_pred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:54:13.57309+00:00
-- url     : https://prove2.me/submissions/0a080478-3628-4e9d-9615-213261053f8a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_pos
import Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_succ_pow

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
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) :
    cyclRadius p (k + 1) ^ (p - 1) = cyclRadius p k / cyclRadius p (k + 1) := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have h : cyclRadius p (k + 1) ^ (p - 1) * cyclRadius p (k + 1) = cyclRadius p k := by
    rw [← pow_succ, Nat.sub_add_cancel hp, cyclRadius_succ_pow (p := p) hk]
  rw [eq_div_iff (cyclRadius_pos (p := p) k).ne', h]
end GroundTheory.PAdicHodge

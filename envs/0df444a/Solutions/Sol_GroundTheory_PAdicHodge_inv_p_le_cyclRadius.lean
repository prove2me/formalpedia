-- Prove2me | solution 1 for GroundTheory.PAdicHodge.inv_p_le_cyclRadius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:57:08.654906+00:00
-- url     : https://prove2.me/submissions/bcebf70e-604f-4c76-9b16-21e1439b2f9c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_pow_totient
import Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_le_one

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
theorem _root_.solution (k : ℕ) : (p : ℝ)⁻¹ ≤ cyclRadius p (k + 1) := by
  rw [← cyclRadius_pow_totient k]
  exact pow_le_of_le_one (norm_nonneg _) (cyclRadius_le_one _)
    (Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)).ne'
end GroundTheory.PAdicHodge

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cyclRadius_pow_totient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:35.984693+00:00
-- url     : https://prove2.me/submissions/dda469cf-4d18-49bd-8cd1-125c8d19ba59

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_pow_totient
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_eq_cyclRadius
import Theorems.Thm_GroundTheory_PAdicHodge_exists_isPrimitiveRoot


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
theorem _root_.solution (k : ℕ) :
    cyclRadius p (k + 1) ^ Nat.totient (p ^ (k + 1)) = (p : ℝ)⁻¹ := by
  rw [← norm_sub_one_eq_cyclRadius (exists_isPrimitiveRoot (p := p) (k + 1)).choose_spec]
  exact norm_sub_one_pow_totient (exists_isPrimitiveRoot (p := p) (k + 1)).choose_spec
end GroundTheory.PAdicHodge

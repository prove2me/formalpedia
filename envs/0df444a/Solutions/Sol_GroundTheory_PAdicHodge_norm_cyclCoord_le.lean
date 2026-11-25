-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_cyclCoord_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:35.948808+00:00
-- url     : https://prove2.me/submissions/f737a364-7419-4513-bec2-837c14e474f0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_eq_one_of_pow_eq_one
import Theorems.Thm_GroundTheory_PAdicHodge_norm_normTrace_cycl_le
import Theorems.Thm_GroundTheory_PAdicHodge_pow_eq_one_mem_cycl


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
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {η : PadicAlgCl p}
    (hη : IsPrimitiveRoot η (p ^ (k + 1))) {y : PadicAlgCl p} (hy : y ∈ cycl p (k + 1)) (i : ℕ) :
    ‖cyclCoord k η y i‖ ≤ p * ‖y‖ := by
  have hηmem : η ∈ cycl p (k + 1) := pow_eq_one_mem_cycl hη.pow_eq_one
  have h := norm_normTrace_cycl_le hk (Nat.le_succ k) (mul_mem hy (pow_mem hηmem (p ^ (k + 1) - i)))
  rwa [norm_mul, norm_pow, norm_eq_one_of_pow_eq_one (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    hη.pow_eq_one, one_pow, mul_one] at h
end GroundTheory.PAdicHodge

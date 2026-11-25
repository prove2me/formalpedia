-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_pow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:00.093801+00:00
-- url     : https://prove2.me/submissions/3bc5017e-e251-432a-878b-817989fcf022

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_eq_one_of_pow_eq_one

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
theorem _root_.solution {ζ : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (hζ : ζ ^ N = 1) (j : ℕ) :
    ‖ζ ^ j - 1‖ ≤ ‖ζ - 1‖ := by
  have h1 : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hN hζ
  rw [← geom_sum_mul, norm_mul]
  have : ‖∑ i ∈ Finset.range j, ζ ^ i‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
      rw [norm_pow, h1, one_pow]
  calc _ ≤ 1 * ‖ζ - 1‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = _ := one_mul _
end GroundTheory.PAdicHodge

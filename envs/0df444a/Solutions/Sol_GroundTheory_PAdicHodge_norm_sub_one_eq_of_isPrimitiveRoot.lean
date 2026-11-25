-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_sub_one_eq_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:43.839043+00:00
-- url     : https://prove2.me/submissions/e425a012-e827-4003-b32a-0e0865f7a425

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_sub_one_le

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
theorem _root_.solution {ζ η : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0)
    (hζ : IsPrimitiveRoot ζ N) (hη : IsPrimitiveRoot η N) : ‖η - 1‖ = ‖ζ - 1‖ := by
  have : NeZero N := ⟨hN⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη.pow_eq_one
  obtain ⟨j, -, hj⟩ := hη.eq_pow_of_pow_eq_one hζ.pow_eq_one
  refine le_antisymm (norm_pow_sub_one_le hN hζ.pow_eq_one i) ?_
  conv_lhs => rw [← hj]
  exact norm_pow_sub_one_le hN hη.pow_eq_one j
end GroundTheory.PAdicHodge

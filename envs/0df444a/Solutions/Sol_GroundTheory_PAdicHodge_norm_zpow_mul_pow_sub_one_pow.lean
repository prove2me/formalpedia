-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_zpow_mul_pow_sub_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:56.482735+00:00
-- url     : https://prove2.me/submissions/df055512-2131-4372-ad6d-19312fa1596c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_pow_totient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
variable {p : ℕ} [Fact p.Prime]
variable {k : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
include hζ
namespace GroundTheory.PAdicHodge
theorem _root_.solution (z : ℤ) (m : ℕ) :
    ((p : ℝ) ^ z * ‖ζ - 1‖ ^ m) ^ Nat.totient (p ^ (k + 1)) =
      (p : ℝ) ^ (z * Nat.totient (p ^ (k + 1)) - m) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hrd := norm_sub_one_pow_totient hζ
  rw [mul_pow, ← pow_mul, mul_comm m, pow_mul, hrd, inv_pow, ← zpow_natCast ((p : ℝ) ^ z),
    ← zpow_mul, ← zpow_natCast (p : ℝ) m, ← zpow_neg, ← zpow_add₀ hp0]
  ring_nf
end GroundTheory.PAdicHodge

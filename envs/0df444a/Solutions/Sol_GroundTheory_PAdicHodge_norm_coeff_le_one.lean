-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_coeff_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:31.941249+00:00
-- url     : https://prove2.me/submissions/758d3a3f-3ba0-48f3-b146-18bbd13976f5

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm
import Theorems.Thm_GroundTheory_PAdicHodge_norm_zpow_mul_pow_sub_one_pow
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_eq_zpow_of_ne_zero
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_GroundTheory_PAdicHodge_one_lt_p_real
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
variable {p : ℕ} [Fact p.Prime]
variable {k : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
include hζ
namespace GroundTheory.PAdicHodge
theorem _root_.solution {c : ℚ_[p]} {i : ℕ} (hi : i < Nat.totient (p ^ (k + 1)))
    (h : ‖c‖ * ‖ζ - 1‖ ^ i ≤ 1) : ‖c‖ ≤ 1 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  obtain ⟨z, hz⟩ := exists_norm_eq_zpow_of_ne_zero (p := p) hc
  rw [hz] at h ⊢
  have h1 : ((p : ℝ) ^ z * ‖ζ - 1‖ ^ i) ^ Nat.totient (p ^ (k + 1)) ≤ 1 :=
    pow_le_one₀ (mul_nonneg (zpow_nonneg (by positivity) _) (pow_nonneg (norm_nonneg _) _)) h
  rw [norm_zpow_mul_pow_sub_one_pow hζ] at h1
  have h2 := (zpow_le_one_iff_right₀ one_lt_p_real).1 h1
  have hz0 : z ≤ 0 := by
    by_contra hz0
    have hz1 : 1 ≤ z := by omega
    have : (Nat.totient (p ^ (k + 1)) : ℤ) ≤ z * Nat.totient (p ^ (k + 1)) := by
      nlinarith
    omega
  exact zpow_le_one_of_nonpos₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le) hz0
end GroundTheory.PAdicHodge

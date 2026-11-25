-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_le_of_normTrace_cycl_succ_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:13.750021+00:00
-- url     : https://prove2.me/submissions/01965389-b9e0-46b5-a58c-af2b3363df69

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_eq_one_of_pow_eq_one
import Theorems.Thm_GroundTheory_PAdicHodge_exists_apply_eq_mul_of_fix
import Theorems.Thm_GroundTheory_PAdicHodge_inv_p_le_norm_pow_sub_one
import Theorems.Thm_GroundTheory_PAdicHodge_cyclCoord_zero
import Theorems.Thm_GroundTheory_PAdicHodge_cyclCoord_sub
import Theorems.Thm_GroundTheory_PAdicHodge_eq_sum_cyclCoord
import Theorems.Thm_GroundTheory_PAdicHodge_norm_cyclCoord_le
import Theorems.Thm_GroundTheory_PAdicHodge_cyclCoord_apply
import Theorems.Thm_GroundTheory_PAdicHodge_map_mem_cycl


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
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k)
    (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hτ : ∀ x ∈ cycl p k, τ x = x)
    {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1))) (hτη : τ η ≠ η)
    {y : PadicAlgCl p} (hy : y ∈ cycl p (k + 1)) (h0 : normTrace (cycl p k) y = 0) :
    ‖y‖ ≤ (p : ℝ) ^ 2 * ‖τ y - y‖ := by
  have hpr := (Fact.out : p.Prime)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
  obtain ⟨ε, hεp, hτη'⟩ := exists_apply_eq_mul_of_fix τ hτ hη
  have hε1 : ε ≠ 1 := by rintro rfl; rw [one_mul] at hτη'; exact hτη hτη'
  have hτy : τ y ∈ cycl p (k + 1) := map_mem_cycl τ hy
  have hw : τ y - y ∈ cycl p (k + 1) := sub_mem hτy hy
  have hcoord : ∀ i ∈ Finset.range p, ‖cyclCoord k η y i‖ ≤ (p : ℝ) ^ 2 * ‖τ y - y‖ := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [cyclCoord_zero hη, h0, norm_zero]; positivity
    have hle : i ≤ p ^ (k + 1) := le_trans hi'.le (Nat.le_self_pow (by omega) p)
    have e : cyclCoord k η (τ y - y) i = (ε ^ i - 1) * cyclCoord k η y i := by
      rw [cyclCoord_sub, cyclCoord_apply hk τ hτ hεp hτη' y hle]; ring
    have h1 := norm_cyclCoord_le hk hη hw i
    rw [e, norm_mul] at h1
    have h2 := inv_p_le_norm_pow_sub_one hεp hε1 hipos hi'
    have h3 : (p : ℝ)⁻¹ * ‖cyclCoord k η y i‖ ≤ p * ‖τ y - y‖ :=
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans h1
    calc ‖cyclCoord k η y i‖ = p * ((p : ℝ)⁻¹ * ‖cyclCoord k η y i‖) := by field_simp
      _ ≤ p * (p * ‖τ y - y‖) := mul_le_mul_of_nonneg_left h3 hp0.le
      _ = _ := by ring
  conv_lhs => rw [eq_sum_cyclCoord hk hη hy]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
  rw [norm_mul, norm_pow, norm_eq_one_of_pow_eq_one (pow_ne_zero _ hpr.ne_zero) hη.pow_eq_one,
    one_pow, mul_one]
  exact hcoord i hi
end GroundTheory.PAdicHodge

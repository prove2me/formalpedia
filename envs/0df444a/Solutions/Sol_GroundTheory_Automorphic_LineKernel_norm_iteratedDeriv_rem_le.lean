-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.norm_iteratedDeriv_rem_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:25.03456+00:00
-- url     : https://prove2.me/submissions/4016d7b3-6ec1-4a32-89e7-bfc66ab381a1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_iteratedDeriv_deriv_cutoff_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_deriv_cutoff
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasCompactSupport_iteratedDeriv_deriv_cutoff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function
open scoped ContDiff FourierTransform
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {r : ℝ} (hr : 0 < r) (q : ℕ) :
    ∃ S, 0 ≤ S ∧ ∀ a, 0 ≤ a → ∀ t,
      ‖iteratedDeriv q (rem a r) t‖ ≤ 2 ^ q * (1 + a) ^ q * exp (-a * r) * S := by
  have hb : ∀ i, ∃ C, ∀ t, ‖iteratedDeriv i (deriv (cutoff r)) t‖ ≤ C := fun i =>
    (hasCompactSupport_iteratedDeriv_deriv_cutoff hr i).exists_bound_of_continuous
      ((contDiff_deriv_cutoff r).continuous_iteratedDeriv i (by exact_mod_cast le_top))
  choose C hC using hb
  refine ⟨∑ i ∈ Finset.range (q + 1), |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
  intro a ha t
  have hE : ContDiff ℝ ∞ fun t : ℝ => exp (-a * t) :=
    contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hrem : rem a r = -fun t => exp (-a * t) * deriv (cutoff r) t := by
    funext t; rfl
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hrem, iteratedFDeriv_neg_apply, norm_neg]
  refine (norm_iteratedFDeriv_mul_le hE (contDiff_deriv_cutoff r) t
    (by exact_mod_cast le_top)).trans ?_
  simp_rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul]
  have hS : ∀ i ∈ Finset.range (q + 1), |C i| ≤ ∑ i ∈ Finset.range (q + 1), |C i| := fun i hi =>
    Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) hi
  calc ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖(-a) ^ i * exp (-a * t)‖ *
        ‖iteratedDeriv (q - i) (deriv (cutoff r)) t‖
      ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
          ((1 + a) ^ q * exp (-a * r) * ∑ i ∈ Finset.range (q + 1), |C i|) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have hiq : i ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hqi : q - i ∈ Finset.range (q + 1) := Finset.mem_range.2 (by omega)
        by_cases ht : t ∈ Icc r (2 * r)
        · have h1 : ‖(-a) ^ i * exp (-a * t)‖ ≤ (1 + a) ^ q * exp (-a * r) := by
            rw [norm_mul, norm_pow, norm_neg, Real.norm_eq_abs, abs_of_nonneg ha,
              Real.norm_eq_abs, abs_of_pos (exp_pos _)]
            have h2 : a ^ i ≤ (1 + a) ^ q := (pow_le_pow_left₀ ha (by linarith) i).trans
              (pow_le_pow_right₀ (by linarith) hiq)
            have h3 : exp (-a * t) ≤ exp (-a * r) := exp_le_exp.2 (by nlinarith [ht.1])
            exact mul_le_mul h2 h3 (exp_pos _).le (by positivity)
          have h4 : ‖iteratedDeriv (q - i) (deriv (cutoff r)) t‖ ≤ ∑ i ∈ Finset.range (q + 1), |C i| :=
            (hC (q - i) t).trans ((le_abs_self _).trans (hS _ hqi))
          exact mul_le_mul h1 h4 (norm_nonneg _) (by positivity)
        · rw [iteratedDeriv_deriv_cutoff_eq_zero hr ht, norm_zero, mul_zero]
          have : 0 ≤ ∑ i ∈ Finset.range (q + 1), |C i| :=
            Finset.sum_nonneg fun i _ => abs_nonneg _
          positivity
    _ = 2 ^ q * (1 + a) ^ q * exp (-a * r) * ∑ i ∈ Finset.range (q + 1), |C i| := by
        rw [← Finset.sum_mul]
        have : ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) = 2 ^ q := by
          exact_mod_cast Nat.sum_range_choose q
        rw [this]; ring
end GroundTheory.Automorphic.LineKernel

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.isHausdorff_span_of_isUnit_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:51:39.381485+00:00
-- url     : https://prove2.me/submissions/14d7bb7a-e9e3-409e-aca7-f82432fd6abb

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_smodEq_span_singleton_pow_iff
import Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_teichmuller_add_mul_p
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_zero
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_eq_zero_iff
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_coeff_zero_pow
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_fontaineTheta_eq_one_of_isUnit_coeff_one
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_coeff_zero_add_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_untilt_coeff_zero
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_eq_zero_of_p_mul_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isDomain_preTilt


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
open WittVector
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {ξ : 𝕎𝒪♭} (hξ : ξ ∈ RingHom.ker θ)
    (h1 : IsUnit (ξ.coeff 1)) : IsHausdorff (Ideal.span {ξ}) 𝕎𝒪♭ := by
  have := isDomain_preTilt (K := K) p
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨v, hv⟩ := exists_eq_teichmuller_add_mul_p ξ
  have hθv := norm_fontaineTheta_eq_one_of_isUnit_coeff_one hv h1
  have hθξ := untilt_coeff_zero_add_eq_zero hξ hv
  suffices H : ∀ m (x : 𝕎𝒪♭), (∀ n, ξ ^ n ∣ x) → (p : 𝕎𝒪♭) ^ m ∣ x by
    refine ⟨fun x hx => IsHausdorff.haus (I := Ideal.span {(p : 𝕎𝒪♭)}) inferInstance x
      fun m => ?_⟩
    rw [smodEq_span_singleton_pow_iff, sub_zero]
    exact H m x fun n => by
      have := hx n
      rwa [smodEq_span_singleton_pow_iff, sub_zero] at this
  by_cases hpO : (p : 𝒪) = 0
  · have hξ0 : ξ.coeff 0 = 0 := by
      rw [hpO, mul_zero, add_zero] at hθξ
      exact (untilt_eq_zero_iff p).1 hθξ
    rw [hξ0, teichmuller_zero, zero_add] at hv
    intro m x hx
    obtain ⟨w, hw⟩ := hx m
    exact ⟨v ^ m * w, by rw [hw, hv, mul_pow]; ring⟩
  have hpK : (p : K) ≠ 0 := fun h => hpO (Subtype.ext (by simpa using h))
  have hp1 : ‖(p : K)‖ < 1 := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
  have hnξ0 := norm_untilt_coeff_zero hξ hv
  rw [hθv, one_mul] at hnξ0
  have hξ0 : ξ.coeff 0 ≠ 0 := by
    intro h
    rw [h, untilt_zero, ZeroMemClass.coe_zero, norm_zero] at hnξ0
    exact hpK (norm_eq_zero.1 hnξ0.symm)
  intro m
  induction m with
  | zero => intro x _; simp
  | succ m ih =>
    intro x hx
    have hx0 : x.coeff 0 = 0 := by
      rw [← untilt_eq_zero_iff p]
      have hle : ∀ n, ‖((PreTilt.untilt (x.coeff 0) : 𝒪) : K)‖ ≤ ‖(p : K)‖ ^ n := by
        intro n
        obtain ⟨w, hw⟩ := hx n
        have hw0 : x.coeff 0 = ξ.coeff 0 ^ n * w.coeff 0 := by
          rw [hw, mul_coeff_zero, coeff_zero_pow]
        rw [hw0, map_mul, map_pow, Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow,
          hnξ0]
        calc ‖(p : K)‖ ^ n * ‖((PreTilt.untilt (w.coeff 0) : 𝒪) : K)‖
            ≤ ‖(p : K)‖ ^ n * 1 := by
              gcongr; exact mem_normInteger.1 (PreTilt.untilt (w.coeff 0)).2
          _ = _ := mul_one _
      have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : K)) hp1
      have h0 := ge_of_tendsto' ht hle
      exact Subtype.ext (norm_le_zero_iff.1 h0)
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1
      ((mem_span_p_iff_coeff_zero_eq_zero x).2 hx0)
    have hy' : ∀ n, ξ ^ n ∣ y := by
      intro n
      obtain ⟨w, hw⟩ := hx n
      have hw0 : w.coeff 0 = 0 := by
        have h := congrArg (fun z : 𝕎𝒪♭ => z.coeff 0) (hy.trans hw)
        rw [mul_charP_coeff_zero, mul_coeff_zero, coeff_zero_pow] at h
        exact (mul_eq_zero.1 h.symm).resolve_left (pow_ne_zero _ hξ0)
      obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.1
        ((mem_span_p_iff_coeff_zero_eq_zero w).2 hw0)
      refine ⟨w', sub_eq_zero.1 (eq_zero_of_p_mul_eq_zero ?_)⟩
      rw [mul_sub, mul_comm (p : 𝕎𝒪♭) y, hy, hw, ← hw']
      ring
    obtain ⟨t, ht⟩ := ih y hy'
    exact ⟨t, by rw [← hy, ht]; ring⟩
end GroundTheory.PAdicHodge.IsPerfectoidField

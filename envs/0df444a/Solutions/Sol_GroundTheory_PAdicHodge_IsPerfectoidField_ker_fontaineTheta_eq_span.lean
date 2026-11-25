-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.ker_fontaineTheta_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:33:50.256366+00:00
-- url     : https://prove2.me/submissions/2d958023-c566-4c5b-aff0-f92a3999c98b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_le_span_singleton_of_forall_mem_eq
import Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_teichmuller_add_mul_p
import Theorems.Thm_GroundTheory_PAdicHodge_coeff_one_teichmuller_add_mul_p
import Theorems.Thm_GroundTheory_PAdicHodge_isUnit_of_isUnit_coeff_zero
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_zero
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_eq_zero_iff
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_dvd_of_norm_untilt_le
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_fontaineTheta_eq_one_of_isUnit_coeff_one
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_coeff_zero_add_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_untilt_coeff_zero

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
    (h1 : IsUnit (ξ.coeff 1)) : RingHom.ker θ = Ideal.span {ξ} := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨v, hv⟩ := exists_eq_teichmuller_add_mul_p ξ
  have hθv := norm_fontaineTheta_eq_one_of_isUnit_coeff_one hv h1
  have hθξ := untilt_coeff_zero_add_eq_zero hξ hv
  refine le_antisymm ?_ (Ideal.span_le.2 (Set.singleton_subset_iff.2 hξ))
  by_cases hpO : (p : 𝒪) = 0
  ·
    have hξ0 : ξ.coeff 0 = 0 := by
      rw [hpO, mul_zero, add_zero] at hθξ
      exact (untilt_eq_zero_iff p).1 hθξ
    have hv0 : IsUnit (v.coeff 0) := by
      have h := congrArg (fun w : 𝕎𝒪♭ => w.coeff 1) hv
      rw [coeff_one_teichmuller_add_mul_p] at h
      rw [h] at h1
      exact (isUnit_pow_iff hp0).1 h1
    have hvu : IsUnit v := isUnit_of_isUnit_coeff_zero hv0
    rw [hξ0, teichmuller_zero, zero_add] at hv
    intro x hx
    obtain ⟨y, hy⟩ := exists_eq_teichmuller_add_mul_p x
    have hx0 : x.coeff 0 = 0 := by
      have h := untilt_coeff_zero_add_eq_zero hx hy
      rw [hpO, mul_zero, add_zero] at h
      exact (untilt_eq_zero_iff p).1 h
    rw [hx0, teichmuller_zero, zero_add] at hy
    rw [Ideal.mem_span_singleton, hy, hv]
    exact mul_dvd_mul_right hvu.dvd _
  · have hpK : (p : K) ≠ 0 := fun h => hpO (Subtype.ext (by simpa using h))
    have hnξ0 := norm_untilt_coeff_zero hξ hv
    rw [hθv, one_mul] at hnξ0
    have hξ0 : ξ.coeff 0 ≠ 0 := by
      intro h
      rw [h, untilt_zero, ZeroMemClass.coe_zero, norm_zero] at hnξ0
      exact hpK (norm_eq_zero.1 hnξ0.symm)
    refine le_span_singleton_of_forall_mem_eq (π := (p : 𝕎𝒪♭)) fun x hx => ?_
    obtain ⟨y, hy⟩ := exists_eq_teichmuller_add_mul_p x
    have hθx := untilt_coeff_zero_add_eq_zero hx hy
    have hnx0 : ‖((PreTilt.untilt (x.coeff 0) : 𝒪) : K)‖ ≤ ‖(p : K)‖ := by
      rw [norm_untilt_coeff_zero hx hy]
      calc ‖((θ y : 𝒪) : K)‖ * ‖(p : K)‖ ≤ 1 * ‖(p : K)‖ := by
            gcongr; exact mem_normInteger.1 (θ y).2
        _ = _ := one_mul _
    obtain ⟨c, hc⟩ := dvd_of_norm_untilt_le p hξ0 (hnx0.trans hnξ0.ge)
    refine ⟨teichmuller p c, y - teichmuller p c * v, ?_, ?_⟩
    · rw [RingHom.mem_ker]
      have hc' : PreTilt.untilt (x.coeff 0) = PreTilt.untilt (ξ.coeff 0) * PreTilt.untilt c := by
        rw [hc, map_mul]
      have h2 : θ (y - teichmuller p c * v) * p = 0 := by
        rw [map_sub, map_mul, fontaineTheta_teichmuller]
        linear_combination hθx - PreTilt.untilt c * hθξ - hc'
      exact (mul_eq_zero.1 h2).resolve_right hpO
    · have hteich : teichmuller p (x.coeff 0) = teichmuller p c * teichmuller p (ξ.coeff 0) := by
        rw [hc, map_mul, mul_comm]
      linear_combination hy - teichmuller p c * hv + hteich
end GroundTheory.PAdicHodge.IsPerfectoidField

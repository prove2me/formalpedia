-- Prove2me | solution 1 for GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:52:06.291516+00:00
-- url     : https://prove2.me/submissions/2ab89b52-27a4-40ad-8ac7-84ad466b2dac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosMulNormSqLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralPointNormSquareBound
namespace GlobalTheory.IntegralPointNormSquareBound
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (h : ∀ v : V, v ≠ 0 → 0 < om v (J v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V, c * ‖v‖ ^ 2 ≤ om v (J v) := by
  have hcont : Continuous fun v : V => om v (J v) := by
    let B : V →ₗ[ℝ] V →L[ℝ] ℝ :=
      (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] V →L[ℝ] ℝ).toLinearMap ∘ₗ om
    have h1 : Continuous B := B.continuous_of_finiteDimensional
    have h2 : Continuous J := J.continuous_of_finiteDimensional
    exact h1.clm_apply h2
  have hcomp : IsCompact (Metric.sphere (0 : V) 1) := by
    haveI : ProperSpace V := FiniteDimensional.proper_real V
    exact isCompact_sphere 0 1
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Metric.sphere (0 : V) 1, c ≤ om u (J u) := by
    rcases (Metric.sphere (0 : V) 1).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun u hu => by rw [he] at hu; exact hu.elim⟩
    · obtain ⟨x, hx, hmin⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
      refine ⟨om x (J x), h x ?_, fun u hu => hmin hu⟩
      rintro rfl
      simp at hx
  refine ⟨c, hc, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv
    simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
      simp [norm_smul, hn.ne']
    have h3 := hle _ hu
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h3
    have h4 : ‖v‖⁻¹ * (‖v‖⁻¹ * om v (J v)) * ‖v‖ ^ 2 = om v (J v) := by
      field_simp
    calc c * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ * (‖v‖⁻¹ * om v (J v)) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = om v (J v) := h4
end GlobalTheory.IntegralPointNormSquareBound

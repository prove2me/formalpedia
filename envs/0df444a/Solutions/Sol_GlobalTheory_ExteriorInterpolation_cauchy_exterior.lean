-- Prove2me | solution 1 for GlobalTheory.ExteriorInterpolation.cauchy_exterior
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:52.067882+00:00
-- url     : https://prove2.me/submissions/a53cb2d2-0e0a-4fdc-a390-40cbc895d7cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsInterpolationExteriorSmallCoeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExteriorInterpolation
namespace GlobalTheory.ExteriorInterpolation
theorem _root_.solution (g : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hg : DifferentiableOn ℂ g {w | r ≤ ‖w‖}) (h0 : Tendsto g (Filter.cocompact ℂ) (𝓝 0))
    (w : ℂ) (hw : r < ‖w‖) :
    ∮ ζ in C(0, r), (ζ - w)⁻¹ * g ζ = -(2 * Real.pi * I * g w) := by
  have hS : {ζ : ℂ | r ≤ ‖ζ‖} ∈ 𝓝 w :=
    Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hw)
      (fun ζ hζ => by simp only [Set.mem_ofPred_eq] at hζ ⊢; exact hζ.le)
  have hgw : DifferentiableAt ℂ g w := hg.differentiableAt hS
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = dslope g w := ⟨_, rfl⟩
  have hFc : ContinuousOn F {ζ : ℂ | r ≤ ‖ζ‖} := by
    rw [hF]
    exact (continuousOn_dslope hS).mpr ⟨hg.continuousOn, hgw⟩
  have main : ∀ R : ℝ, ‖w‖ < R → (∮ ζ in C(0, r), (ζ - w)⁻¹ * g ζ)
      = (∮ ζ in C(0, R), (ζ - w)⁻¹ * g ζ) - 2 * Real.pi * I * g w := by
    intro R hR
    have hrR : r ≤ R := (hw.trans hR).le
    have hsub : ∀ ρ, r ≤ ρ → Metric.sphere (0 : ℂ) ρ ⊆ {ζ : ℂ | r ≤ ‖ζ‖} := by
      intro ρ h1 ζ hζ
      rw [mem_sphere_zero_iff_norm] at hζ
      show r ≤ ‖ζ‖
      rw [hζ]
      exact h1
    have split : ∀ ρ, r ≤ ρ → ‖w‖ ≠ ρ → (∮ ζ in C(0, ρ), (ζ - w)⁻¹ * g ζ)
        = g w * (∮ ζ in C(0, ρ), (ζ - w)⁻¹) + ∮ ζ in C(0, ρ), F ζ := by
      intro ρ h1 hne
      have hρ : 0 ≤ ρ := hr.le.trans h1
      have hne' : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ, ζ - w ≠ 0 := by
        intro ζ hζ h
        rw [mem_sphere_zero_iff_norm] at hζ
        rw [sub_eq_zero] at h
        rw [h] at hζ
        exact hne hζ
      have c1 : ContinuousOn (fun ζ : ℂ => (ζ - w)⁻¹) (Metric.sphere (0 : ℂ) ρ) :=
        (continuousOn_id.sub continuousOn_const).inv₀ hne'
      rw [← smul_eq_mul (g w), ← circleIntegral.integral_smul (g w) _ 0 ρ,
        ← circleIntegral.integral_add
          (show CircleIntegrable (fun ζ => g w • (ζ - w)⁻¹) 0 ρ from
            (ContinuousOn.circleIntegrable hρ (by fun_prop (disch := exact hne'))))
          ((hFc.mono (hsub ρ h1)).circleIntegrable hρ)]
      apply circleIntegral.integral_congr hρ
      intro ζ hζ
      have hz := hne' ζ hζ
      simp only [hF, dslope_of_ne _ (sub_ne_zero.mp hz), slope_def_field, smul_eq_mul]
      field_simp
      ring
    have hann : (∮ ζ in C(0, R), F ζ) = ∮ ζ in C(0, r), F ζ := by
      apply circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
        (Set.countable_singleton w)
      · refine hFc.mono ?_
        intro ζ hζ
        have := hζ.2
        rw [Metric.mem_ball, dist_zero_right, not_lt] at this
        exact this
      · intro ζ hζ
        have hζ1 := hζ.1.2
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hζ1
        have hζw : ζ ≠ w := hζ.2
        rw [hF, differentiableAt_dslope_of_ne hζw]
        exact hg.differentiableAt
          (Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hζ1)
            (fun x hx => by simp only [Set.mem_ofPred_eq] at hx ⊢; exact hx.le))
    have hzero : (∮ ζ in C(0, r), (ζ - w)⁻¹) = 0 := by
      have hne0 : ∀ ζ ∈ Metric.closedBall (0 : ℂ) r, ζ - w ≠ 0 := by
        intro ζ hζ h
        rw [Metric.mem_closedBall, dist_zero_right] at hζ
        rw [sub_eq_zero] at h
        rw [h] at hζ
        linarith
      apply circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      · exact (continuousOn_id.sub continuousOn_const).inv₀ hne0
      · intro ζ hζ
        exact (differentiableAt_id.sub_const w).inv
          (hne0 ζ (Metric.ball_subset_closedBall hζ.1))
    have hone : (∮ ζ in C(0, R), (ζ - w)⁻¹) = 2 * Real.pi * I :=
      circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hR)
    rw [split r le_rfl (ne_of_gt hw), split R hrR (ne_of_lt hR), hann, hzero, hone]
    ring
  obtain ⟨S, hS'⟩ : ∃ S, S = ∮ ζ in C(0, r), (ζ - w)⁻¹ * g ζ := ⟨_, rfl⟩
  rw [← hS']
  have hK : ∀ ε > 0, ‖S + 2 * Real.pi * I * g w‖ ≤ 4 * Real.pi * ε := by
    intro ε hε
    have hev : ∀ᶠ ζ in cocompact ℂ, ‖g ζ‖ ≤ ε := by
      filter_upwards [h0 (Metric.closedBall_mem_nhds 0 hε)] with ζ hζ
      simpa using hζ
    obtain ⟨K, hKc, hKs⟩ := (Filter.hasBasis_cocompact.eventually_iff).mp hev
    obtain ⟨M, hM⟩ := hKc.isBounded.subset_closedBall 0
    set R : ℝ := max (M + 1) (2 * ‖w‖ + 1) with hRdef
    have hR1 : M + 1 ≤ R := le_max_left _ _
    have hR2 : 2 * ‖w‖ + 1 ≤ R := le_max_right _ _
    have hRpos : 0 < R := by linarith [norm_nonneg w]
    have hwR : ‖w‖ < R := by linarith [norm_nonneg w]
    rw [hS', main R hwR]
    simp only [sub_add_cancel]
    have hb : ∀ ζ ∈ Metric.sphere (0 : ℂ) R, ‖(ζ - w)⁻¹ * g ζ‖ ≤ 2 / R * ε := by
      intro ζ hζ
      rw [mem_sphere_zero_iff_norm] at hζ
      have hgz : ‖g ζ‖ ≤ ε := by
        apply hKs
        intro hK'
        have := hM hK'
        rw [Metric.mem_closedBall, dist_zero_right] at this
        linarith
      have hd : R / 2 ≤ ‖ζ - w‖ := by
        have := norm_sub_norm_le ζ w
        linarith
      have hinv : ‖ζ - w‖⁻¹ ≤ 2 / R := by
        rw [show 2 / R = (R / 2)⁻¹ by field_simp]
        exact inv_anti₀ (by positivity) hd
      rw [norm_mul, norm_inv]
      exact mul_le_mul hinv hgz (norm_nonneg _) (by positivity)
    calc ‖∮ ζ in C(0, R), (ζ - w)⁻¹ * g ζ‖ ≤ 2 * Real.pi * R * (2 / R * ε) :=
          circleIntegral.norm_integral_le_of_norm_le_const hRpos.le hb
      _ = 4 * Real.pi * ε := by field_simp; ring
  have h00 : ‖S + 2 * Real.pi * I * g w‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hpos'
    have hpos := lt_of_not_ge hpos'
    have h8 := hK (‖S + 2 * Real.pi * I * g w‖ / (8 * Real.pi)) (by positivity)
    have : 4 * Real.pi * (‖S + 2 * Real.pi * I * g w‖ / (8 * Real.pi))
        = ‖S + 2 * Real.pi * I * g w‖ / 2 := by
      field_simp
      ring
    rw [this] at h8
    linarith
  have := norm_eq_zero.mp h00
  linear_combination this
end GlobalTheory.ExteriorInterpolation

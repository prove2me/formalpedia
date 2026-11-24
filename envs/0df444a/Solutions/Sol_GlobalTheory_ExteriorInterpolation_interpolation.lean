-- Prove2me | solution 1 for GlobalTheory.ExteriorInterpolation.interpolation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:31:25.780803+00:00
-- url     : https://prove2.me/submissions/4e921c6e-e8d1-4985-a256-fe52108d226a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsInterpolationExteriorSmallCoeffs
import Theorems.Thm_GlobalTheory_ExteriorInterpolation_exists_divided
import Theorems.Thm_GlobalTheory_ExteriorInterpolation_cauchy_exterior
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
namespace GlobalTheory.ExteriorInterpolation
private theorem circleIntegral_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    (∮ z in C(c, R), ∑ i ∈ s, f i z) = ∑ i ∈ s, ∮ z in C(c, R), f i z := by
  simp only [circleIntegral, Finset.smul_sum]
  exact intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).out)
end GlobalTheory.ExteriorInterpolation
end

set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExteriorInterpolation
namespace GlobalTheory.ExteriorInterpolation
theorem _root_.solution : ∀ (l : ℕ) (z : Fin l → ℂ) (g : ℂ → ℂ) (r G : ℝ), 0 < r → r ≤ 1 → (∀ i, r < ‖z i‖ ∧ ‖z i‖ ≤ 1) → DifferentiableOn ℂ g {w | r ≤ ‖w‖} → Tendsto g (Filter.cocompact ℂ) (𝓝 0) → (∀ w : ℂ, ‖w‖ = r → ‖g w‖ ≤ G * ‖∏ i, (w - z i)‖) → ∃ c : Fin l → ℂ, (∀ i, ∑ j, c j * z i ^ (j : ℕ) = g (z i)) ∧ ∑ j, ‖c j‖ ≤ 4 ^ l * r * G := by
  intro l z g r G hr hr1 hz hg h0 hG
  obtain ⟨b, hbc, hbb, hbid⟩ := exists_divided l z (fun i => (hz i).2)
  have hPne : ∀ ζ ∈ Metric.sphere (0 : ℂ) r, ∏ k, (ζ - z k) ≠ 0 := by
    intro ζ hζ
    rw [Finset.prod_ne_zero_iff]
    intro k _ h
    rw [mem_sphere_zero_iff_norm] at hζ
    rw [sub_eq_zero] at h
    have := (hz k).1
    rw [← h, hζ] at this
    exact lt_irrefl _ this
  have hsph : Metric.sphere (0 : ℂ) r ⊆ {w : ℂ | r ≤ ‖w‖} := by
    intro ζ hζ
    rw [mem_sphere_zero_iff_norm] at hζ
    show r ≤ ‖ζ‖
    rw [hζ]
  have hcont : ∀ j, ContinuousOn (fun ζ => g ζ / (∏ k, (ζ - z k)) * b j ζ)
      (Metric.sphere (0 : ℂ) r) := by
    intro j
    refine ContinuousOn.mul ?_ (hbc j).continuousOn
    exact (hg.continuousOn.mono hsph).div (by fun_prop) hPne
  obtain ⟨c, hc⟩ : ∃ c : Fin l → ℂ,
      c = fun j => -(2 * (Real.pi : ℂ) * I)⁻¹ * ∮ ζ in C(0, r), g ζ / (∏ k, (ζ - z k)) * b j ζ :=
    ⟨_, rfl⟩
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  refine ⟨c, fun i => ?_, ?_⟩
  · have hwi := (hz i).1
    have e1 : ∑ j, c j * z i ^ (j : ℕ) = -(2 * (Real.pi : ℂ) * I)⁻¹ *
        ∑ j : Fin l, ∮ ζ in C(0, r), z i ^ (j : ℕ) • (g ζ / (∏ k, (ζ - z k)) * b j ζ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [circleIntegral.integral_smul, hc, smul_eq_mul]
      ring
    rw [e1, ← circleIntegral_finset_sum' Finset.univ
      (fun (j : Fin l) ζ => z i ^ (j : ℕ) • ((g ζ / ∏ k, (ζ - z k)) * b j ζ)) 0 r
      (fun j _ => ContinuousOn.circleIntegrable hr.le ((hcont j).const_smul (z i ^ (j : ℕ))))]
    have e2 : (∮ ζ in C(0, r), ∑ j : Fin l, z i ^ (j : ℕ) • (g ζ / (∏ k, (ζ - z k)) * b j ζ))
        = ∮ ζ in C(0, r), (ζ - z i)⁻¹ * g ζ := by
      apply circleIntegral.integral_congr hr.le
      intro ζ hζ
      have hPζ := hPne ζ hζ
      have hzne : ζ - z i ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        rw [mem_sphere_zero_iff_norm, h] at hζ
        rw [hζ] at hwi
        exact lt_irrefl _ hwi
      have e := hbid ζ (z i)
      have hPz : ∏ k, (z i - z k) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
      rw [hPz, sub_zero] at e
      have hsum : ∑ j, b j ζ * z i ^ (j : ℕ) = (∏ k, (ζ - z k)) / (ζ - z i) :=
        eq_div_of_mul_eq hzne e
      have e3 : ∑ j : Fin l, z i ^ (j : ℕ) • (g ζ / (∏ k, (ζ - z k)) * b j ζ)
          = g ζ / (∏ k, (ζ - z k)) * ∑ j, b j ζ * z i ^ (j : ℕ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_eq_mul]
        ring
      simp only
      rw [e3, hsum]
      field_simp
    rw [e2, cauchy_exterior g r hr hg h0 (z i) hwi]
    field_simp
  · have hsph1 : ∀ ζ ∈ Metric.sphere (0 : ℂ) r, ‖ζ‖ = r := fun ζ hζ =>
      mem_sphere_zero_iff_norm.mp hζ
    have hG0 : 0 ≤ G := by
      have hmem : ((r : ℂ)) ∈ Metric.sphere (0 : ℂ) r := by
        rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have hpos : 0 < ‖∏ k, ((r : ℂ) - z k)‖ := norm_pos_iff.mpr (hPne _ hmem)
      have h1 := hG (r : ℂ) (hsph1 _ hmem)
      by_contra hneg
      have hlt : G * ‖∏ k, ((r : ℂ) - z k)‖ < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpos
      linarith [norm_nonneg (g (r : ℂ))]
    have hbound : ∀ j, ∀ ζ ∈ Metric.sphere (0 : ℂ) r,
        ‖g ζ / (∏ k, (ζ - z k)) * b j ζ‖ ≤ G * 2 ^ l := by
      intro j ζ hζ
      have hpos : 0 < ‖∏ k, (ζ - z k)‖ := norm_pos_iff.mpr (hPne ζ hζ)
      have hq : ‖g ζ‖ / ‖∏ k, (ζ - z k)‖ ≤ G := by
        rw [div_le_iff₀ hpos]
        exact hG ζ (hsph1 ζ hζ)
      have hb := hbb j ζ (by rw [hsph1 ζ hζ]; exact hr1)
      rw [norm_mul, norm_div]
      exact mul_le_mul hq hb (norm_nonneg _) hG0
    have hcj : ∀ j, ‖c j‖ ≤ 2 ^ l * (r * G) := by
      intro j
      have hI := circleIntegral.norm_integral_le_of_norm_le_const hr.le (hbound j)
      have hn : ‖-(2 * (Real.pi : ℂ) * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
        rw [norm_neg, norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
        norm_num
      rw [hc]
      simp only
      rw [norm_mul, hn]
      calc (2 * Real.pi)⁻¹ * ‖∮ ζ in C(0, r), g ζ / (∏ k, (ζ - z k)) * b j ζ‖
          ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * r * (G * 2 ^ l)) := by
            gcongr
        _ = 2 ^ l * (r * G) := by
            field_simp
    have hl : (l : ℝ) ≤ 2 ^ l := by exact_mod_cast (Nat.lt_two_pow_self (n := l)).le
    calc ∑ j, ‖c j‖ ≤ ∑ _j : Fin l, 2 ^ l * (r * G) := Finset.sum_le_sum (fun j _ => hcj j)
      _ = (l : ℝ) * (2 ^ l * (r * G)) := by simp
      _ ≤ 2 ^ l * (2 ^ l * (r * G)) := by
          gcongr
      _ = 4 ^ l * r * G := by
          rw [show (4 : ℝ) ^ l = 2 ^ l * 2 ^ l by rw [← mul_pow]; norm_num]
          ring
end GlobalTheory.ExteriorInterpolation

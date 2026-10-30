-- Prove2me | solution 1 for MonopolyDemandUncertainty.SBSMP.fact_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:50:48.001748+00:00
-- url     : https://prove2.me/submissions/de3ce16b-804e-4d0c-a854-d7c0f433aab7

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

open MeasureTheory Set

namespace Aux_MDU_F2
open MonopolyDemandUncertainty.SBSMP

lemma dens_cont (E : Economy) (h1 : E.Condition1) (i : Fin 2) : Continuous (E.dens i) := by
  unfold Economy.dens
  exact ((h1.1 i).continuous_deriv (by norm_num)).neg

lemma D_diff (E : Economy) (h1 : E.Condition1) (i : Fin 2) : Differentiable ℝ (E.D i) :=
  (h1.1 i).differentiable (by norm_num)

lemma dens_pos (E : Economy) (h1 : E.Condition1) (i : Fin 2) (v : ℝ) (hv : v ∈ E.V) :
    0 < E.dens i v := by
  unfold Economy.dens; linarith [h1.2 i v hv]

lemma Z_strictAnti (E : Economy) (h2 : E.Condition2) : StrictAntiOn E.Z E.V := by
  have hd : ∀ v ∈ E.V, DifferentiableAt ℝ E.Z v := fun v hv =>
    differentiableAt_of_deriv_ne_zero (ne_of_lt (h2 v hv))
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun v hv => (hd v hv).continuousAt.continuousWithinAt
  · intro v hv
    exact h2 v (interior_subset hv)

/-- `D_i(v) = ∫_v^{v̄} dens_i`. -/
lemma D_eq_int (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (v : ℝ) :
    E.D i v = ∫ s in v..E.vhi, E.dens i s := by
  unfold Economy.dens
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_deriv_eq_sub
    (fun x _ => D_diff E h1 i x)
    (((h1.1 i).continuous_deriv (by norm_num)).intervalIntegrable _ _), hE.D_vhi i]
  ring

lemma D_antitone (E : Economy) (h1 : E.Condition1) (i : Fin 2) : StrictAntiOn (E.D i) E.V := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact (D_diff E h1 i).continuous.continuousOn
  · intro v hv; exact h1.2 i v (interior_subset hv)

lemma dens_mono (E : Economy) (h1 : E.Condition1) (h3 : E.Condition3) (i : Fin 2) :
    MonotoneOn (E.dens i) E.V := by
  apply (strictMonoOn_of_deriv_pos (convex_Icc _ _) (dens_cont E h1 i).continuousOn _).monotoneOn
  intro v hv
  have hv' := interior_subset hv
  have : deriv (E.dens i) v = - deriv (deriv (E.D i)) v := by
    unfold Economy.dens
    exact deriv.neg
  rw [this]; linarith [h3 i v hv']

lemma D_nonneg (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (v : ℝ)
    (hv : v ∈ E.V) : 0 ≤ E.D i v := by
  rcases eq_or_lt_of_le hv.2 with h | h
  · rw [h, hE.D_vhi i]
  · have := D_antitone E h1 i hv ⟨le_trans hv.1 h.le, le_refl _⟩ h
    rw [hE.D_vhi i] at this; exact this.le

lemma part_a (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2) (v : ℝ)
    (hv1 : E.vlo ≤ v) (hv2 : v < E.vhi) :
    E.D 0 v / E.dens 0 v < E.D 1 v / E.dens 1 v := by
  have hvV : v ∈ E.V := ⟨hv1, hv2.le⟩
  have p0 := dens_pos E h1 0 v hvV
  have p1 := dens_pos E h1 1 v hvV
  rw [div_lt_div_iff₀ p0 p1, D_eq_int E hE h1 0 v, D_eq_int E hE h1 1 v]
  -- dens1(v) ∫ dens0 < dens0(v) ∫ dens1
  have hpos : 0 < ∫ s in v..E.vhi, (E.dens 0 v * E.dens 1 s - E.dens 1 v * E.dens 0 s) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact ((continuous_const.mul (dens_cont E h1 1)).sub
        (continuous_const.mul (dens_cont E h1 0))).intervalIntegrable _ _
    · intro s hs
      have hsV : s ∈ E.V := ⟨le_trans hv1 hs.1.le, hs.2.le⟩
      have hZ := Z_strictAnti E h2 hvV hsV hs.1
      unfold Economy.Z at hZ
      rw [div_lt_div_iff₀ (dens_pos E h1 1 s hsV) p1] at hZ
      linarith
    · exact hv2
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hpos
  · linarith
  · exact (continuous_const.mul (dens_cont E h1 1)).intervalIntegrable _ _
  · exact (continuous_const.mul (dens_cont E h1 0)).intervalIntegrable _ _

end Aux_MDU_F2

open MonopolyDemandUncertainty.SBSMP Aux_MDU_F2 in
theorem solution (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (h3 : E.Condition3) :
    (∀ v, E.vlo ≤ v → v < E.vhi → E.D 0 v / E.dens 0 v < E.D 1 v / E.dens 1 v) ∧
      ∀ p₁ ∈ E.V, ∀ p₂ ∈ E.V, p₁ = -(E.D 0 p₁ / deriv (E.D 0) p₁) →
        p₂ = -(E.D 1 p₂ / deriv (E.D 1) p₂) → p₁ < p₂ := by
  refine ⟨part_a E hE h1 h2, ?_⟩
  intro p₁ hp₁ p₂ hp₂ e1 e2
  have r1 : p₁ = E.D 0 p₁ / E.dens 0 p₁ := by
    unfold Economy.dens; rw [div_neg]; exact e1
  have r2 : p₂ = E.D 1 p₂ / E.dens 1 p₂ := by
    unfold Economy.dens; rw [div_neg]; exact e2
  by_contra hle
  rw [not_lt] at hle
  rcases eq_or_lt_of_le hp₂.2 with h | h
  · have : p₂ = 0 := by rw [r2, h, hE.D_vhi 1, zero_div]
    linarith [hE.vlo_nonneg, hE.vlo_lt_vhi]
  · have ha := part_a E hE h1 h2 p₂ hp₂.1 h
    rw [← r2] at ha
    -- ratio0 antitone: ratio0(p₁) ≤ ratio0(p₂)
    have hD : E.D 0 p₁ ≤ E.D 0 p₂ := (D_antitone E h1 0).antitoneOn hp₂ hp₁ hle
    have hd : E.dens 0 p₂ ≤ E.dens 0 p₁ := dens_mono E h1 h3 0 hp₂ hp₁ hle
    have hD0 := D_nonneg E hE h1 0 p₁ hp₁
    have q1 := dens_pos E h1 0 p₁ hp₁
    have q2 := dens_pos E h1 0 p₂ hp₂
    have hr : E.D 0 p₁ / E.dens 0 p₁ ≤ E.D 0 p₂ / E.dens 0 p₂ := by
      rw [div_le_div_iff₀ q1 q2]
      nlinarith
    linarith

-- Prove2me | solution 1 for MonopolyDemandUncertainty.SBSMP.claim_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:54:41.593829+00:00
-- url     : https://prove2.me/submissions/7f8ac8ce-fa06-437c-b78f-f4f649e905bb

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

open MeasureTheory Set

namespace Aux_MDU_C4
open MonopolyDemandUncertainty.SBSMP

lemma prob_pos (E : Economy) (hE : E.Valid) (i : Fin 2) : 0 < E.prob i := by
  fin_cases i
  · simp [Economy.prob]; linarith [hE.α₁_pos]
  · simp [Economy.prob]; linarith [hE.α₁_lt_one]

lemma dens_pos (E : Economy) (h1 : E.Condition1) (i : Fin 2) (v : ℝ) (hv : v ∈ E.V) :
    0 < E.dens i v := by
  unfold Economy.dens; linarith [h1.2 i v hv]

lemma dens_cont (E : Economy) (h1 : E.Condition1) (i : Fin 2) : Continuous (E.dens i) := by
  unfold Economy.dens
  exact ((h1.1 i).continuous_deriv (by norm_num)).neg

lemma Z_strictAnti (E : Economy) (h2 : E.Condition2) : StrictAntiOn E.Z E.V := by
  have hd : ∀ v ∈ E.V, DifferentiableAt ℝ E.Z v := fun v hv =>
    differentiableAt_of_deriv_ne_zero (ne_of_lt (h2 v hv))
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun v hv => (hd v hv).continuousAt.continuousWithinAt
  · intro v hv
    exact h2 v (interior_subset hv)

/-- `w₁(v) w₂(b) ≤ w₁(b) w₂(v)` for `b ≤ v` in `V`. -/
lemma ratio_mono (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (b v : ℝ) (hbV : b ∈ E.V) (hvV : v ∈ E.V) (hbv : b ≤ v) :
    (E.prob 0 * E.dens 0 v) * (E.prob 1 * E.dens 1 b) ≤
      (E.prob 0 * E.dens 0 b) * (E.prob 1 * E.dens 1 v) := by
  rcases eq_or_lt_of_le hbv with h | h
  · rw [← h]
  · have hz := Z_strictAnti E h2 hbV hvV h
    unfold Economy.Z at hz
    rw [div_lt_div_iff₀ (dens_pos E h1 1 v hvV) (dens_pos E h1 1 b hbV)] at hz
    have := mul_lt_mul_of_pos_left hz (mul_pos (prob_pos E hE 0) (prob_pos E hE 1))
    nlinarith

end Aux_MDU_C4

open MonopolyDemandUncertainty.SBSMP Aux_MDU_C4 in
theorem solution (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (h3 : E.Condition3) (h4 : E.Condition4ii) (a₁ a₂ b : ℝ) (hlo : E.vlo ≤ a₂)
    (h21 : a₂ < a₁) (h1b : a₁ < b) (hb : b ≤ E.vhi) :
    E.Claim4Feasible a₁ a₂ b ![fun _ => E.claim4T1 a₁ a₂, fun _ => b] ∧
      ∀ s : Fin 2 → ℝ → ℝ, E.Claim4Feasible a₁ a₂ b s →
        ∫ v in Icc b E.vhi, ∑ i, s i v * E.prob i * E.dens i v ≤
          ∫ v in Icc b E.vhi,
            (E.claim4T1 a₁ a₂ * E.prob 0 * E.dens 0 v + b * E.prob 1 * E.dens 1 v) := by
  have ha1V : a₁ ∈ E.V := ⟨by linarith, by linarith⟩
  have hbV : b ∈ E.V := ⟨by linarith, hb⟩
  set T := E.claim4T1 a₁ a₂ with hT
  -- bounds on T
  have q0 := dens_pos E h1 0 a₁ ha1V
  have q1 := dens_pos E h1 1 a₁ ha1V
  have r0 := prob_pos E hE 0
  have r1 := prob_pos E hE 1
  have hfrac : E.prob 1 / (E.prob 0 * E.Z a₁) =
      (E.prob 1 * E.dens 1 a₁) / (E.prob 0 * E.dens 0 a₁) := by
    unfold Economy.Z; field_simp
  have hfrac_pos : 0 < E.prob 1 / (E.prob 0 * E.Z a₁) := by
    rw [hfrac]; positivity
  have hfrac_lt : E.prob 1 / (E.prob 0 * E.Z a₁) < 1 := by
    rw [hfrac, div_lt_one (by positivity)]; exact h4 a₁ ha1V
  have hTeq : T = a₁ - (a₁ - a₂) * (E.prob 1 / (E.prob 0 * E.Z a₁)) := by
    rw [hT, Economy.claim4T1]; ring
  have hTle : T ≤ b := by
    rw [hTeq]; nlinarith
  have hTge : 0 ≤ T := by
    rw [hTeq]; nlinarith [hE.vlo_nonneg]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [← hT]
  · intro v _; simp
  · intro i; fin_cases i
    · simp; exact ⟨hTge, hTle⟩
    · simp; linarith [hE.vlo_nonneg]
  · simp; linarith
  · simp [← hT]
  · intro s ⟨c1, c2, c3, _, _⟩
    have hs1 := (c3 1).2
    have hsub : ∀ v ∈ Icc b E.vhi, v ∈ E.V := fun v hv => ⟨by linarith [hv.1], hv.2⟩
    have hc : Continuous (fun v => T * E.prob 0 * E.dens 0 v + b * E.prob 1 * E.dens 1 v) :=
      ((continuous_const.mul (dens_cont E h1 0)).add (continuous_const.mul (dens_cont E h1 1)))
    have hRnn : 0 ≤ ∫ v in Icc b E.vhi,
        (T * E.prob 0 * E.dens 0 v + b * E.prob 1 * E.dens 1 v) := by
      apply setIntegral_nonneg measurableSet_Icc
      intro v hv
      have hvV := hsub v hv
      have := dens_pos E h1 0 v hvV
      have := dens_pos E h1 1 v hvV
      have : 0 ≤ b := le_trans hE.vlo_nonneg hbV.1
      positivity
    -- (s₀(b) - T) w₁(b) ≤ (b - s₁(b)) w₂(b)
    have kb : (s 0 b - T) * (E.prob 0 * E.dens 0 b) ≤ (b - s 1 b) * (E.prob 1 * E.dens 1 b) := by
      nlinarith [c1]
    have hpt : ∀ v ∈ Icc b E.vhi, (∑ i, s i v * E.prob i * E.dens i v) ≤
        T * E.prob 0 * E.dens 0 v + b * E.prob 1 * E.dens 1 v := by
      intro v hv
      have hvV := hsub v hv
      have kv : s 0 v * (E.prob 0 * E.dens 0 v) + s 1 v * (E.prob 1 * E.dens 1 v) ≤
          s 0 b * (E.prob 0 * E.dens 0 v) + s 1 b * (E.prob 1 * E.dens 1 v) := by
        rcases eq_or_lt_of_le hv.1 with h | h
        · rw [← h]
        · have hh := c2 v ⟨h, hv.2⟩
          simp only [Fin.sum_univ_two] at hh
          nlinarith [hh]
      have hZ := ratio_mono E hE h1 h2 b v hbV hvV hv.1
      set A := E.prob 0 * E.dens 0 b
      set B := E.prob 1 * E.dens 1 b
      set C := E.prob 0 * E.dens 0 v
      set Dd := E.prob 1 * E.dens 1 v
      have hA : 0 < A := mul_pos r0 (dens_pos E h1 0 b hbV)
      have hC : 0 < C := mul_pos r0 (dens_pos E h1 0 v hvV)
      have s1 : (s 0 b - T) * A * C ≤ (b - s 1 b) * B * C :=
        mul_le_mul_of_nonneg_right kb hC.le
      have s2 : (b - s 1 b) * (C * B) ≤ (b - s 1 b) * (A * Dd) :=
        mul_le_mul_of_nonneg_left hZ (by linarith)
      have s3 : (s 0 b - T) * C ≤ (b - s 1 b) * Dd := by
        have : ((s 0 b - T) * C) * A ≤ ((b - s 1 b) * Dd) * A := by nlinarith
        exact le_of_mul_le_mul_right this hA
      rw [Fin.sum_univ_two]
      simp only [mul_assoc] at kv s3 ⊢
      nlinarith
    by_cases hint : IntegrableOn (fun v => ∑ i, s i v * E.prob i * E.dens i v) (Icc b E.vhi)
    · exact setIntegral_mono_on hint hc.integrableOn_Icc measurableSet_Icc hpt
    · rw [integral_undef hint]; exact hRnn

-- Prove2me | solution 1 for MonopolyDemandUncertainty.SBSMP.lemma_2_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:46:28.833229+00:00
-- url     : https://prove2.me/submissions/e6daf605-5c6b-49cc-a1b0-bbdd0b7fcad6

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

open MeasureTheory Set

namespace Aux_MDU_L2i
open MonopolyDemandUncertainty.SBSMP

lemma prob_pos (E : Economy) (hE : E.Valid) (i : Fin 2) : 0 < E.prob i := by
  fin_cases i
  · simp [Economy.prob]; linarith [hE.α₁_pos]
  · simp [Economy.prob]; linarith [hE.α₁_lt_one]

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

end Aux_MDU_L2i

open MonopolyDemandUncertainty.SBSMP Aux_MDU_L2i in
theorem solution (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (M : Mechanism) (hBIC : E.IsBIC M) (hEIR : E.IsEIR M) :
    ∀ v₁ ∈ E.onlySet M 0, ∀ v₁₂ ∈ E.bothSet M, v₁ < v₁₂ := by
  intro a ha b hb
  obtain ⟨haV, hax0, hax1⟩ := ha
  have hax1' : M.x 1 a = false := hax1 1 (by decide)
  obtain ⟨hbV, hbx⟩ := hb
  have hbx0 := hbx 0
  have hbx1 := hbx 1
  by_contra hlt
  replace hlt := not_lt.mp hlt
  have hne : a ≠ b := by
    rintro rfl; rw [hbx1] at hax1'; exact Bool.noConfusion hax1'
  have hgt : b < a := lt_of_le_of_ne hlt (Ne.symm hne)
  -- weights
  set A := E.prob 0 * E.dens 0 b
  set B := E.prob 1 * E.dens 1 b
  set C := E.prob 0 * E.dens 0 a
  set Dd := E.prob 1 * E.dens 1 a
  have hA : 0 < A := mul_pos (prob_pos E hE 0) (dens_pos E h1 0 b hbV)
  have hB : 0 < B := mul_pos (prob_pos E hE 1) (dens_pos E h1 1 b hbV)
  have hC : 0 < C := mul_pos (prob_pos E hE 0) (dens_pos E h1 0 a haV)
  have hD : 0 < Dd := mul_pos (prob_pos E hE 1) (dens_pos E h1 1 a haV)
  have hZ : E.Z a < E.Z b := Z_strictAnti E h2 hbV haV hgt
  have hZ' : C * B < A * Dd := by
    unfold Economy.Z at hZ
    have p0 := dens_pos E h1 0 a haV
    have p1 := dens_pos E h1 1 a haV
    have q0 := dens_pos E h1 0 b hbV
    have q1 := dens_pos E h1 1 b hbV
    rw [div_lt_div_iff₀ p1 q1] at hZ
    have r0 := prob_pos E hE 0
    have r1 := prob_pos E hE 1
    have : E.prob 0 * E.prob 1 * (E.dens 0 a * E.dens 1 b) <
        E.prob 0 * E.prob 1 * (E.dens 0 b * E.dens 1 a) :=
      mul_lt_mul_of_pos_left hZ (mul_pos r0 r1)
    simp only [A, B, C, Dd]; nlinarith [this]
  have i1 := hBIC b hbV a haV
  have i2 := hBIC a haV b hbV
  simp only [Economy.payoff, Fin.sum_univ_two, ind, hax0, hax1', hbx0, hbx1] at i1 i2
  simp only [if_true] at i1 i2
  -- i1 : (b - t0 a)*1*A + (b - t1 a)*0*B ≤ (b - t0 b)*1*A + (b - t1 b)*1*B
  have hT2 := (hEIR 1 b hbV).2
  set T1 := M.t 0 b
  set T2 := M.t 1 b
  set p := M.t 0 a
  have e1 : (T1 - p) * A ≤ (b - T2) * B := by
    have : (b - p) * 1 * E.prob 0 * E.dens 0 b + (b - M.t 1 a) * 0 * E.prob 1 * E.dens 1 b ≤
      (b - T1) * 1 * E.prob 0 * E.dens 0 b + (b - T2) * 1 * E.prob 1 * E.dens 1 b := i1
    simp only [A, B]; nlinarith [this]
  have e2 : (a - T2) * Dd ≤ (T1 - p) * C := by
    have : (a - T1) * 1 * E.prob 0 * E.dens 0 a + (a - T2) * 1 * E.prob 1 * E.dens 1 a ≤
      (a - p) * 1 * E.prob 0 * E.dens 0 a + (a - M.t 1 a) * 0 * E.prob 1 * E.dens 1 a := i2
    simp only [C, Dd]; nlinarith [this]
  have s1 : (a - T2) * Dd * A ≤ (b - T2) * B * C := by
    have := mul_le_mul_of_nonneg_right e2 hA.le
    have := mul_le_mul_of_nonneg_right e1 hC.le
    nlinarith
  have s2 : (b - T2) * (C * B) ≤ (b - T2) * (A * Dd) :=
    mul_le_mul_of_nonneg_left hZ'.le (by linarith)
  have s3 : (b - T2) * (A * Dd) < (a - T2) * (A * Dd) :=
    mul_lt_mul_of_pos_right (by linarith) (mul_pos hA hD)
  nlinarith

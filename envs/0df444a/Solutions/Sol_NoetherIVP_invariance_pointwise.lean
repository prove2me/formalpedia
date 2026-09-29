-- Prove2me | solution 1 for NoetherIVP.invariance_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T16:17:38.834138+00:00
-- url     : https://prove2.me/submissions/089f1ba8-ecee-4fb3-86bf-962657c65222

import Mathlib
import Definitions.Def_NoetherIVP_core

open Finset NoetherIVP MeasureTheory Metric

namespace NoetherAux

/-- A continuous function on `ℝⁿ` whose integral over every closed ball vanishes and which is
positive at a point contradicts itself: near that point it stays above half its value, and the
ball around the point has positive finite measure. -/
private lemma not_pos_of_setIntegral_closedBall_eq_zero {n : ℕ} (G : (Fin n → ℝ) → ℝ)
    (hcont : Continuous G)
    (hI : ∀ (c : Fin n → ℝ) (r : ℝ), (∫ y in Metric.closedBall c r, G y) = 0)
    (x : Fin n → ℝ) (hpos : 0 < G x) : False := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hcont x (G x / 2) (by linarith)
  have hr : (0:ℝ) < δ / 2 := by linarith
  have hsub : ∀ y ∈ Metric.closedBall x (δ/2), G x / 2 ≤ G y := by
    intro y hy
    have hd : dist y x < δ := lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by linarith)
    have h := hball y hd
    rw [Real.dist_eq] at h
    linarith [(abs_lt.mp h).1]
  have hintG : IntegrableOn G (Metric.closedBall x (δ/2)) :=
    hcont.continuousOn.integrableOn_compact (isCompact_closedBall x (δ/2))
  have hintC : IntegrableOn (fun _ : Fin n → ℝ => G x / 2) (Metric.closedBall x (δ/2)) :=
    continuousOn_const.integrableOn_compact (isCompact_closedBall x (δ/2))
  have h1 : (∫ y in Metric.closedBall x (δ/2), (G x / 2))
      ≤ ∫ y in Metric.closedBall x (δ/2), G y :=
    setIntegral_mono_on hintC hintG measurableSet_closedBall hsub
  rw [hI x (δ/2), setIntegral_const] at h1
  have hvol : 0 < (volume (Metric.closedBall x (δ/2))).toReal := by
    have h2 := measure_closedBall_pos (volume : Measure (Fin n → ℝ)) x hr
    have h3 : volume (Metric.closedBall x (δ/2)) ≠ ⊤ := measure_closedBall_lt_top.ne
    exact ENNReal.toReal_pos h2.ne' h3
  rw [smul_eq_mul, Measure.real] at h1
  nlinarith

/-- A continuous function on `ℝⁿ` whose integral over every closed ball vanishes is identically
zero. -/
lemma eq_zero_of_setIntegral_closedBall_eq_zero {n : ℕ} (G : (Fin n → ℝ) → ℝ)
    (hcont : Continuous G)
    (hI : ∀ (c : Fin n → ℝ) (r : ℝ), (∫ y in Metric.closedBall c r, G y) = 0) :
    ∀ x, G x = 0 := by
  intro x
  rcases lt_trichotomy (G x) 0 with h | h | h
  · exact (not_pos_of_setIntegral_closedBall_eq_zero (fun y => -G y) hcont.neg
      (fun c r => by simp [integral_neg, hI c r]) x (by linarith)).elim
  · exact h
  · exact (not_pos_of_setIntegral_closedBall_eq_zero G hcont hI x h).elim

end NoetherAux

theorem solution {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u du : (Fin n → ℝ) → Fin m → ℝ) (dx : (Fin n → ℝ) → Fin n → ℝ)
    (hcont : Continuous fun y => varF f u du y + divg (fun z l => lagr f u z * dx z l) y)
    (hI : ∀ (c : Fin n → ℝ) (r : ℝ),
      (∫ y in Metric.closedBall c r,
        (varF f u du y + divg (fun z l => lagr f u z * dx z l) y)) = 0) :
    ∀ x : Fin n → ℝ,
      varF f u du x + divg (fun z l => lagr f u z * dx z l) x = 0 :=
  NoetherAux.eq_zero_of_setIntegral_closedBall_eq_zero
    (fun y => varF f u du y + divg (fun z l => lagr f u z * dx z l) y) hcont hI

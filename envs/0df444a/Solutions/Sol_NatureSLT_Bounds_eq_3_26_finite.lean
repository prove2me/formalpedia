-- Prove2me | solution 1 for NatureSLT.Bounds.eq_3_26_finite
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:48:44.089977+00:00
-- url     : https://prove2.me/submissions/a5ebb3eb-5949-4113-a2cd-88386ef2fff3

import Mathlib

open MeasureTheory
open scoped ENNReal

noncomputable def g69f_F : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance g69f_F_prob : IsProbabilityMeasure g69f_F := ⟨by
  simp [g69f_F]
  rw [← two_mul, ENNReal.mul_inv_cancel] <;> norm_num⟩

theorem g69f_F_int : ∫ x, (fun (_ : Unit) (z : Bool) => if z then (1:ℝ) else 0) () x ∂g69f_F = 1 / 2 := by
  simp only [g69f_F]
  rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp))]
  simp [integral_dirac]

theorem g69f_X_lt : -(2 * Real.log (7/10)) < 1 := by
  have : Real.log (10/7) ≤ 10/7 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h2 : Real.log (10/7) = - Real.log (7/10) := by
    rw [show (10/7 : ℝ) = (7/10)⁻¹ by norm_num, Real.log_inv]
  linarith

theorem g69f_sX_lt : Real.sqrt (-(2 * Real.log (7/10))) < 1 := by
  rw [Real.sqrt_lt' one_pos]; simpa using g69f_X_lt

theorem solution : ¬ (∀ {Z Λ : Type} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    [Fintype Λ] [Nonempty Λ]
    (Q : Λ → Z → ℝ) (A B : ℝ) (hAB : A < B) (hQA : ∀ α z, A ≤ Q α z) (hQB : ∀ α z, Q α z ≤ B)
    (hQmeas : ∀ α, Measurable (Q α))
    (ℓ : ℕ) (hℓ : 0 < ℓ) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1),
    let 𝓔 : ℝ := 2 * (Real.log (Fintype.card Λ) - Real.log η) / ℓ
    ENNReal.ofReal (1 - η) ≤ (Measure.pi fun _ : Fin ℓ => F)
        {z | ∀ α, ∫ x, Q α x ∂F ≤ (1 / (ℓ : ℝ)) * ∑ i, Q α (z i) + (B - A) / 2 * Real.sqrt 𝓔 ∧
          ∫ x, Q α x ∂F ≥ (1 / (ℓ : ℝ)) * ∑ i, Q α (z i) - (B - A) / 2 * Real.sqrt 𝓔}) := by
  intro h
  have H := h (Z := Bool) (Λ := Unit) g69f_F (fun _ z => if z then (1:ℝ) else 0) 0 1
    (by norm_num) (fun _ z => by split_ifs <;> norm_num) (fun _ z => by split_ifs <;> norm_num)
    (fun _ => measurable_of_countable _) 1 one_pos (7/10) (by norm_num) (by norm_num)
  simp only at H
  have hX := g69f_X_lt
  have hs := g69f_sX_lt
  have hempty : {z : Fin 1 → Bool | ∀ α : Unit,
      ∫ x, (fun (_ : Unit) (z : Bool) => if z then (1:ℝ) else 0) α x ∂g69f_F ≤
        (1 / ((1:ℕ) : ℝ)) * ∑ i, (fun (_ : Unit) (z : Bool) => if z then (1:ℝ) else 0) α (z i) +
          (1 - 0) / 2 * Real.sqrt (2 * (Real.log (Fintype.card Unit) - Real.log (7/10)) / (1:ℕ)) ∧
      ∫ x, (fun (_ : Unit) (z : Bool) => if z then (1:ℝ) else 0) α x ∂g69f_F ≥
        (1 / ((1:ℕ) : ℝ)) * ∑ i, (fun (_ : Unit) (z : Bool) => if z then (1:ℝ) else 0) α (z i) -
          (1 - 0) / 2 * Real.sqrt (2 * (Real.log (Fintype.card Unit) - Real.log (7/10)) / (1:ℕ))} = ∅ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hz
    have h1 := hz ()
    rw [g69f_F_int] at h1
    simp only [Fin.sum_univ_one] at h1
    cases hz0 : z 0 <;> simp [hz0] at h1 <;> linarith [h1.1, h1.2]
  rw [hempty, measure_empty] at H
  simp at H
  norm_num at H

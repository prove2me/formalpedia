-- Prove2me | solution 1 for LSWCuttingPlane.ChasingZero.drift_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T02:02:42.255836+00:00
-- url     : https://prove2.me/submissions/0899c50f-735f-4218-b096-1eb98ae1cf58

import Mathlib
import Definitions.Def_LSWCuttingPlane_ChasingZero_Setting
import Theorems.Thm_LSWCuttingPlane_ChasingZero_exp_taylor_bound

open MeasureTheory
open LSWCuttingPlane.ChasingZero

namespace C0Drift

noncomputable def pot {m : ℕ} (α : ℝ) (x : Fin m → ℝ) : ℝ :=
  ∑ j, (Real.exp (α * x j) + Real.exp (-(α * x j)))

lemma coord_bound (α c x d : ℝ) (hα : 0 ≤ α) (hd : |d| ≤ c) :
    Real.exp (α * (x + d)) + Real.exp (-(α * (x + d))) ≤
      Real.exp (α * x) + Real.exp (-(α * x)) + α * (Real.exp (α * x) - Real.exp (-(α * x))) * d
        + 1 / 2 * α ^ 2 * d ^ 2 * Real.exp (α * c) * (Real.exp (α * x) + Real.exp (-(α * x))) := by
  have h1 := exp_taylor_bound.2 c d x α hd
  have h2 := exp_taylor_bound.2 c d x (-α) hd
  have e1 : α * (x + d) = α * x + α * d := by ring
  have e2 : -(α * (x + d)) = -α * x + -α * d := by ring
  have e3 : Real.exp (α * x + |α| * c) = Real.exp (α * x) * Real.exp (α * c) := by
    rw [abs_of_nonneg hα, Real.exp_add]
  have e4 : Real.exp (-α * x + |-α| * c) = Real.exp (-(α * x)) * Real.exp (α * c) := by
    rw [abs_neg, abs_of_nonneg hα, Real.exp_add]; ring_nf
  rw [e2, e1]
  rw [e3] at h1
  rw [e4] at h2
  have e5 : -α * x = -(α * x) := by ring
  rw [e5] at h2 ⊢
  nlinarith [h1, h2]

lemma pot_le {m : ℕ} (α B : ℝ) (hα : 0 ≤ α) (x : Fin m → ℝ) (hx : ∀ j, |x j| ≤ B) :
    pot α x ≤ m * (2 * Real.exp (α * B)) := by
  unfold pot
  have h : ∀ j, Real.exp (α * x j) + Real.exp (-(α * x j)) ≤ 2 * Real.exp (α * B) := by
    intro j
    have h1 : α * x j ≤ α * B := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hx j)) hα
    have h2 : -(α * x j) ≤ α * B := by
      have := mul_le_mul_of_nonneg_left (le_trans (neg_le_abs (x j)) (hx j)) hα
      linarith
    linarith [Real.exp_le_exp.mpr h1, Real.exp_le_exp.mpr h2]
  have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h j)
  simpa using this


lemma Phi_eq_pot {m : ℕ} (α : ℝ) (x : Fin m → ℝ) : Phi α x = pot α x := by
  unfold Phi pot
  rw [Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring_nf

end C0Drift

open C0Drift in
theorem solution {m : ℕ} [NeZero m] (ν : Measure (Fin m → ℝ)) [IsProbabilityMeasure ν]
    (c α : ℝ) (hc : 0 < c) (hα : 0 ≤ α) (x : Fin m → ℝ)
    (hnorm : ∀ᵐ Δ ∂ν, ∑ i, (Δ i) ^ 2 ≤ c ^ 2)
    (hmean : ∀ i, ∫ Δ, Δ i ∂ν = 0) :
    ∫ Δ, Phi α (x + Δ) ∂ν ≤ Phi α x + α ^ 2 * Real.exp (α * c) * c ^ 2 * eta α x := by
  set η := eta α x with hη
  have hplus : ∀ i, Real.exp (α * x i) ≤ η := fun i =>
    le_trans (Finset.le_sup' (fun i => Real.exp (α * x i)) (Finset.mem_univ i)) (le_max_left _ _)
  have hminus : ∀ i, Real.exp (-(α * x i)) ≤ η := by
    intro i
    rw [hη]; unfold eta
    refine le_trans ?_ (le_max_right _ _)
    have := Finset.le_sup' (fun i => Real.exp (-α * x i)) (Finset.mem_univ i)
    rw [neg_mul] at this
    exact this
  have hη0 : 0 ≤ η := le_trans (Real.exp_pos _).le (hplus ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩)
  have habs : ∀ Δ : Fin m → ℝ, ∑ i, (Δ i) ^ 2 ≤ c ^ 2 → ∀ i, |Δ i| ≤ c := by
    intro Δ h i
    have : Δ i ^ 2 ≤ c ^ 2 := le_trans
      (Finset.single_le_sum (f := fun j => Δ j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)) h
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  set A : Fin m → ℝ := fun i => α * (Real.exp (α * x i) - Real.exp (-(α * x i))) with hA
  set K := α ^ 2 * Real.exp (α * c) * c ^ 2 * η with hK
  -- pointwise bound
  have hpt : ∀ᵐ Δ ∂ν, Phi α (x + Δ) ≤ Phi α x + ∑ i, A i * Δ i + K := by
    filter_upwards [hnorm] with Δ hΔ
    rw [Phi_eq_pot, Phi_eq_pot]
    unfold pot
    have hterm : ∀ i, Real.exp (α * (x + Δ) i) + Real.exp (-(α * (x + Δ) i)) ≤
        (Real.exp (α * x i) + Real.exp (-(α * x i))) + A i * Δ i
          + α ^ 2 * Real.exp (α * c) * η * Δ i ^ 2 := by
      intro i
      have h1 := coord_bound α c (x i) (Δ i) hα (habs Δ hΔ i)
      simp only [Pi.add_apply]
      have h2 : 1 / 2 * α ^ 2 * Δ i ^ 2 * Real.exp (α * c) *
          (Real.exp (α * x i) + Real.exp (-(α * x i))) ≤ α ^ 2 * Real.exp (α * c) * η * Δ i ^ 2 := by
        have h0 : 0 ≤ 1 / 2 * α ^ 2 * Δ i ^ 2 * Real.exp (α * c) := by positivity
        have := mul_le_mul_of_nonneg_left (add_le_add (hplus i) (hminus i)) h0
        nlinarith
      simp only [hA]
      linarith
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    have heq : ∑ j, (Real.exp (α * x j) + Real.exp (-(α * x j))) + ∑ i, A i * Δ i +
        α ^ 2 * Real.exp (α * c) * η * ∑ i, Δ i ^ 2 = ∑ i, ((Real.exp (α * x i) +
          Real.exp (-(α * x i))) + A i * Δ i + α ^ 2 * Real.exp (α * c) * η * Δ i ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [← heq] at hs
    have hK' : α ^ 2 * Real.exp (α * c) * η * ∑ i, Δ i ^ 2 ≤ K := by
      rw [hK]
      have h0 : 0 ≤ α ^ 2 * Real.exp (α * c) * η := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hΔ h0]
    linarith
  -- integrability
  have hΔint : ∀ i, Integrable (fun Δ : Fin m → ℝ => Δ i) ν := by
    intro i
    refine Integrable.of_bound (measurable_pi_apply i).aestronglyMeasurable c ?_
    filter_upwards [hnorm] with Δ hΔ
    rw [Real.norm_eq_abs]; exact habs Δ hΔ i
  have hcont : Continuous (fun Δ : Fin m → ℝ => Phi α (x + Δ)) := by
    unfold Phi; fun_prop
  have hPint : Integrable (fun Δ => Phi α (x + Δ)) ν := by
    refine Integrable.of_bound hcont.aestronglyMeasurable
      (m * (2 * Real.exp (α * (‖x‖ + c)))) ?_
    filter_upwards [hnorm] with Δ hΔ
    rw [Phi_eq_pot, Real.norm_eq_abs, abs_of_nonneg (by unfold pot; positivity)]
    apply pot_le α _ hα
    intro j
    simp only [Pi.add_apply]
    have := norm_le_pi_norm x j
    rw [Real.norm_eq_abs] at this
    linarith [abs_add_le (x j) (Δ j), habs Δ hΔ j]
  have hB : Integrable (fun Δ : Fin m → ℝ => ∑ i, A i * Δ i) ν :=
    integrable_finsetSum _ (fun i _ => (hΔint i).const_mul (A i))
  have hC : Integrable (fun Δ : Fin m → ℝ => Phi α x + ∑ i, A i * Δ i) ν :=
    (integrable_const _).add hB
  refine (integral_mono_ae hPint (hC.add (integrable_const K)) hpt).trans (le_of_eq ?_)
  have e1 := integral_add hC (integrable_const (μ := ν) K)
  have e2 := integral_add (integrable_const (μ := ν) (Phi α x)) hB
  have e3 := integral_finsetSum (μ := ν) Finset.univ (fun i _ => (hΔint i).const_mul (A i))
  try simp only at e1 e2 e3
  simp only [Pi.add_apply]
  rw [e1, e2, e3]
  simp [integral_const_mul, hmean]

-- Prove2me | solution 1 for MasulloRH.riemannHypothesis_of_cofinal_negative_theta_gram
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T12:02:34.107809+00:00
-- url     : https://prove2.me/submissions/0bd0ea6c-bd4e-41a2-9a8c-14aa86e40ba8

import Theorems.Thm_MasulloRH_theta_gram_margin_iff_not_posSemidef
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Linarith

open MasulloRH.GaussianApproximation MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

theorem solution
    (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ (m : ℕ) (y : Fin m → ℚ),
    let δ : ℝ := 1 / (16 * ((n : ℝ) + 1))
    let u : Fin (m + 1) → ℝ → ℂ := Fin.cons (pulse n) (fun i x => theta (x - (y i : ℝ)))
    let G : Matrix (Fin (m+1)) (Fin (m+1)) ℂ := fun i j =>
      ∫ x : ℝ, (Real.exp (2*(3/4)*x + 2*(1/4-δ)*|x|) : ℂ) * conj (u i x) * u j x
    let K : Matrix (Fin (m+1)) (Fin (m+1)) ℝ := fun i j => (G i j).re
    ¬ (K - Matrix.single 0 0 (δ / 2)).PosSemidef) :
    RiemannHypothesis := by
  apply MasulloRH.finite_theta_approximation_excludes_rectangle_zeros.2
  intro N
  obtain ⟨n,hn,m,y,hneg⟩ := h N
  obtain ⟨a,ha⟩ := (MasulloRH.theta_gram_margin_iff_not_posSemidef n m y).2 hneg
  refine ⟨n,hn,m,a,y,?_⟩
  let δ : ℝ := 1/(16*((n:ℝ)+1))
  let A := fun i : Fin m => ((a i).1 : ℂ) + ((a i).2 : ℂ)*Complex.I
  let Y := fun i : Fin m => (y i : ℝ)
  have hd : 0 < δ := by dsimp only [δ]; positivity
  have facts := MasulloRH.finite_theta_approximation_excludes_rectangle_zeros.1
    m (n:ℝ) (3/4) (1/4-δ) δ A Y (Nat.cast_nonneg n) hd (by linarith) (by linarith)
  have gap : energy (3/4) (1/4-δ) (residual n A Y) < δ/2 := by
    rw [facts.2.2.1]
    exact ha
  have hexp : (1/2:ℝ) ≤ Real.exp (-(1/2:ℝ)) := by
    linarith [Real.add_one_le_exp (-(1/2:ℝ))]
  change energy (3/4) (1/4-δ) (residual n A Y) < δ*Real.exp (-(1/2:ℝ))
  exact gap.trans_le (by simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hexp hd.le)

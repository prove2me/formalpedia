-- Prove2me | solution 1 for MasulloRH.theta_gram_negative_direction_at_every_scale_of_RH
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:23:46.30171+00:00
-- url     : https://prove2.me/submissions/a55c71df-54da-4fc8-a81f-ae861e984405

import Theorems.Thm_MasulloRH_finite_theta_energy_approximation_of_mertens_bound
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros
import Theorems.Thm_MasulloRH_theta_gram_margin_iff_not_posSemidef
import Mathlib.Tactic.Linarith

open MasulloRH.GaussianApproximation MeasureTheory
open scoped BigOperators ComplexConjugate

/-- Under RH the specified negative Gram direction exists at every natural scale. -/
theorem solution (hRH : RiemannHypothesis) (n : ℕ) :
    ∃ (m : ℕ) (y : Fin m → ℚ),
    let δ : ℝ := 1 / (16 * ((n : ℝ) + 1))
    let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse n) (fun i x => theta (x-(y i:ℝ)))
    let G : Matrix (Fin (m+1)) (Fin (m+1)) ℂ := fun i j =>
      ∫ x : ℝ, (Real.exp (2*(3/4)*x+2*(1/4-δ)*|x|):ℂ)*conj (u i x)*u j x
    let K : Matrix (Fin (m+1)) (Fin (m+1)) ℝ := fun i j => (G i j).re
    ¬ (K-Matrix.single 0 0 (δ/2)).PosSemidef := by
  let δ : ℝ := 1/(16*((n:ℝ)+1))
  have hd : 0<δ := by dsimp only [δ];positivity
  have hsmall : δ≤1/16 := by
    dsimp only [δ]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have hM := moebius_summatory_rpow_bound_of_riemannHypothesis hRH (δ/2) (by positivity)
  obtain ⟨m,a,y,_,he⟩ := MasulloRH.finite_theta_energy_approximation_of_mertens_bound
    (1/2+δ/2) (3/4) (1/4-δ) n (δ/2) (by linarith) (by linarith) (Nat.cast_nonneg _)
    (by linarith) (by linarith) hM (by positivity)
  refine ⟨m,y,(MasulloRH.theta_gram_margin_iff_not_posSemidef n m y).1 ⟨a,?_⟩⟩
  have h := (MasulloRH.finite_theta_approximation_excludes_rectangle_zeros.1 m (n:ℝ) (3/4) (1/4-δ) δ
    (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))
    (Nat.cast_nonneg _) hd (by linarith) (by linarith)).2.2.1
  rw [h] at he
  exact he

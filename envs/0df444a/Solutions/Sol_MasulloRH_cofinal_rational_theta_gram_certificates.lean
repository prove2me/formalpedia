-- Prove2me | solution 1 for MasulloRH.cofinal_rational_theta_gram_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T04:06:38.469575+00:00
-- url     : https://prove2.me/submissions/107c13b0-33ef-4d3b-9468-54015eb87df8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Theorems.Thm_MasulloRH_cofinal_rational_theta_gram_interval_tables
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros
import Mathlib

open MasulloRH MasulloRH.GaussianApproximation MeasureTheory Finset
open scoped BigOperators ComplexConjugate

private theorem quadratic_re_le_of_entry_error {ι : Type} [Fintype ι]
    (A Q : ι → ι → ℂ) (d : ι → ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hentry : ∀ i j, ‖A i j-Q i j‖ ≤ η) :
    (∑ i, ∑ j, conj (d i)*d j*A i j).re ≤
      (∑ i, ∑ j, conj (d i)*d j*Q i j).re +
        η * (∑ i, (|(d i).re|+|(d i).im|))^2 := by
  classical
  have hdiff : (∑ i, ∑ j, conj (d i)*d j*A i j) -
      (∑ i, ∑ j, conj (d i)*d j*Q i j) =
      ∑ i, ∑ j, conj (d i)*d j*(A i j-Q i j) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hn : ‖(∑ i, ∑ j, conj (d i)*d j*A i j) -
      (∑ i, ∑ j, conj (d i)*d j*Q i j)‖ ≤ η * (∑ i, ‖d i‖)^2 := by
    rw [hdiff]
    calc
      _ ≤ ∑ i, ‖∑ j, conj (d i)*d j*(A i j-Q i j)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖conj (d i)*d j*(A i j-Q i j)‖ :=
        Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
      _ ≤ ∑ i, ∑ j, ‖d i‖*‖d j‖*η := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (hentry i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ((∑ i, ‖d i‖)*(∑ j, ‖d j‖))*η := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = η * (∑ i, ‖d i‖)^2 := by ring
  have hl1 : (∑ i, ‖d i‖)^2 ≤ (∑ i, (|(d i).re|+|(d i).im|))^2 := by
    apply (sq_le_sq₀ (Finset.sum_nonneg (fun i _ => norm_nonneg _))
      (Finset.sum_nonneg (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)))).mpr
    exact Finset.sum_le_sum (fun i _ => Complex.norm_le_abs_re_add_abs_im (d i))
  have hb := hn.trans (mul_le_mul_of_nonneg_left hl1 hη)
  have hr := Complex.re_le_norm ((∑ i, ∑ j, conj (d i)*d j*A i j) -
      (∑ i, ∑ j, conj (d i)*d j*Q i j))
  rw [Complex.sub_re] at hr
  linarith

theorem solution :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      let δ : ℝ := 1/(16*((n:ℝ)+1))
      energy (3/4) (1/4-δ) (residual n
         (fun i => ((a i).1 : ℂ) + ((a i).2 : ℂ)*Complex.I) (fun i => (y i : ℝ))) <
          δ * Real.exp (-(1/2:ℝ)) := by
  intro N
  obtain ⟨n,hn,m,a,y,R,η,hη,hrest⟩ := cofinal_rational_theta_gram_interval_tables N
  refine ⟨n,hn,m,a,y,?_⟩
  let δ : ℝ := 1/(16*((n:ℝ)+1))
  let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse n)
    (fun i x => theta (x-(y i:ℝ)))
  let d : Fin (m+1) → ℂ := Fin.cons 1
    (fun i => -(((a i).1:ℂ)+((a i).2:ℂ)*Complex.I))
  let A : Fin (m+1) → Fin (m+1) → ℂ := fun i j =>
    ∫ x : ℝ, (Real.exp (2*(3/4)*x+2*(1/4-δ)*|x|):ℂ)*conj (u i x)*u j x
  let Q : Fin (m+1) → Fin (m+1) → ℂ := fun i j =>
    ((R i j).1:ℂ)+((R i j).2:ℂ)*Complex.I
  have hentry : ∀ i j, ‖A i j-Q i j‖ ≤ (η:ℝ) := hrest.1
  have hcert : (∑ i, ∑ j, conj (d i)*d j*Q i j).re +
      (η:ℝ)*(∑ i, (|(d i).re|+|(d i).im|))^2 < δ/2 := hrest.2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hηr : 0 ≤ (η:ℝ) := by exact_mod_cast hη
  have hfull := finite_theta_approximation_excludes_rectangle_zeros.1 m (n:ℝ)
    (3/4) (1/4-δ) δ
    (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))
    (Nat.cast_nonneg n) hδ (by linarith) (by linarith)
  have henergy : energy (3/4) (1/4-δ) (residual n
      (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))) =
      (∑ i, ∑ j, conj (d i)*d j*A i j).re := hfull.2.2.1
  change energy (3/4) (1/4-δ) (residual n
      (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))) <
        δ*Real.exp (-(1/2:ℝ))
  rw [henergy]
  apply lt_of_lt_of_le ((quadratic_re_le_of_entry_error A Q d (η:ℝ) hηr hentry).trans_lt hcert)
  have he : (1/2:ℝ) ≤ Real.exp (-(1/2:ℝ)) := by
    linarith [Real.add_one_le_exp (-(1/2:ℝ))]
  have h := mul_le_mul_of_nonneg_left he hδ.le
  nlinarith

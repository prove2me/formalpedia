-- Prove2me | solution 2 for MasulloRH.cofinal_rational_theta_gram_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:34:15.317203+00:00
-- url     : https://prove2.me/submissions/8e3e9128-7983-49b3-915b-016368f0ccc0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_moebius_bound
import Theorems.Thm_MasulloRH_finite_theta_energy_approximation_of_mertens_bound
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros
import Theorems.Thm_ordered_dirichlet_convergence_implies_little_o_partial_sums
import Theorems.Thm_MasulloRH_finite_rational_complex_gram_certificate
import Definitions.Def_MasulloRH_GaussianThetaApproximation

-- Step 1: `mathlib_riemannHypothesis` implies `moebius_dirichlet_partialSum_tendsto_of_half_lt` (accepted reduction of `moebius_dirichlet_partialSum_tendsto_of_half_lt`).
section

theorem moebius_dirichlet_partialSum_tendsto_of_half_lt (σ : ℝ) (hσ : 1 / 2 < σ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ))
      Filter.atTop (nhds L) :=
  moebius_dirichlet_partialSum_tendsto_of_moebius_bound σ hσ
    (moebius_summatory_rpow_bound_of_riemannHypothesis mathlib_riemannHypothesis)

end

-- Step 2: `moebius_dirichlet_partialSum_tendsto_of_half_lt` implies `MasulloRH.cofinal_exact_theta_gram_margin` (accepted reduction of `MasulloRH.cofinal_exact_theta_gram_margin`).
section

open MasulloRH.GaussianApproximation MeasureTheory Filter Asymptotics
open scoped BigOperators ComplexConjugate

set_option autoImplicit false

private theorem mertensBoundOfRealSeries (σ : ℝ) (hσ : 1 / 2 < σ) :
    (fun k : ℕ => ∑ i ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius i : ℂ))
      =O[atTop] (fun k : ℕ => (k : ℝ) ^ σ) := by
  obtain ⟨L, hReal⟩ := moebius_dirichlet_partialSum_tendsto_of_half_lt σ hσ
  have hCast (k : ℕ) :
      ((∑ i ∈ Finset.Icc 1 k,
        (ArithmeticFunction.moebius i : ℝ) * (i : ℝ) ^ (-σ) : ℝ) : ℂ) =
      ∑ i ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius i : ℂ) / (i : ℂ) ^ (σ : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.ofReal_cpow (Nat.cast_nonneg i), Complex.ofReal_neg,
      Complex.cpow_neg, div_eq_mul_inv]
    push_cast
    rfl
  have hComplex :
      Tendsto (fun k : ℕ => ∑ i ∈ Finset.Icc 1 k,
        (ArithmeticFunction.moebius i : ℂ) / (i : ℂ) ^ (σ : ℂ)) atTop (nhds (L : ℂ)) := by
    convert (Complex.continuous_ofReal.tendsto L).comp hReal using 1
    exact (funext hCast).symm
  exact (ordered_dirichlet_convergence_implies_little_o_partial_sums
    (fun i => (ArithmeticFunction.moebius i : ℂ)) (by linarith) hComplex).isBigO

-- The height and strip parameters are as in sflicht's Prove2Me reduction
-- 352d2158-765a-432d-bd01-3cd5d073710f.
theorem MasulloRH.cofinal_exact_theta_gram_margin :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
        let δ : ℝ := 1 / (16 * ((n : ℝ) + 1))
        let u : Fin (m + 1) → ℝ → ℂ := Fin.cons (pulse n)
          (fun i x => theta (x - (y i : ℝ)))
        let d : Fin (m + 1) → ℂ := Fin.cons 1
          (fun i => -(((a i).1 : ℂ) + ((a i).2 : ℂ) * Complex.I))
        (∑ i, ∑ j, conj (d i) * d j *
          (∫ x : ℝ,
            (Real.exp (2 * (3 / 4) * x + 2 * (1 / 4 - δ) * |x|) : ℂ) *
              conj (u i x) * u j x)).re < δ / 2 := by
  intro N
  let δ : ℝ := 1 / (16 * ((N : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδMax : δ ≤ 1 / 16 := by
    dsimp [δ]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hWidth : 0 ≤ 1 / 4 - δ := by linarith
  have hLeft : 1 / 2 + δ / 2 < 3 / 4 - (1 / 4 - δ) := by linarith
  have hRight : 3 / 4 + (1 / 4 - δ) < 1 := by linarith
  obtain ⟨m, a, y, _, hEnergy⟩ :=
    MasulloRH.finite_theta_energy_approximation_of_mertens_bound
      (1 / 2 + δ / 2) (3 / 4) (1 / 4 - δ) N (δ / 2)
      (by positivity) hWidth (by positivity) hLeft hRight
      (mertensBoundOfRealSeries _ (by linarith)) (by positivity)
  refine ⟨N, le_rfl, m, a, y, ?_⟩
  let aC : Fin m → ℂ := fun i => ((a i).1 : ℂ) + ((a i).2 : ℂ) * Complex.I
  let yR : Fin m → ℝ := fun i => (y i : ℝ)
  have hGram := (MasulloRH.finite_theta_approximation_excludes_rectangle_zeros.1
    m N (3 / 4) (1 / 4 - δ) δ aC yR (by positivity) hδ (by linarith) hRight).2.2.1
  change energy (3 / 4) (1 / 4 - δ) (residual N aC yR) < δ / 2 at hEnergy
  rw [hGram] at hEnergy
  exact hEnergy

end

-- Step 3: `MasulloRH.cofinal_exact_theta_gram_margin` implies `MasulloRH.cofinal_rational_theta_gram_interval_tables` (accepted reduction of `MasulloRH.cofinal_rational_theta_gram_interval_tables`).
section

open MasulloRH.GaussianApproximation MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

theorem MasulloRH.cofinal_rational_theta_gram_interval_tables :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ)
      (R : Fin (m+1) → Fin (m+1) → ℚ × ℚ) (η : ℚ), 0 ≤ η ∧
      let δ : ℝ := 1/(16*((n:ℝ)+1))
      let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse n)
        (fun i x => theta (x-(y i:ℝ)))
      let d : Fin (m+1) → ℂ := Fin.cons 1
        (fun i => -(((a i).1:ℂ)+((a i).2:ℂ)*Complex.I))
      let Q : Fin (m+1) → Fin (m+1) → ℂ :=
        fun i j => ((R i j).1:ℂ)+((R i j).2:ℂ)*Complex.I
      (∀ i j, ‖(∫ x : ℝ, (Real.exp (2*(3/4)*x+2*(1/4-δ)*|x|):ℂ) *
        conj (u i x) * u j x) - Q i j‖ ≤ (η:ℝ)) ∧
      (∑ i, ∑ j, conj (d i)*d j*Q i j).re +
        (η:ℝ) * (∑ i, (|(d i).re|+|(d i).im|))^2 < δ/2 := by
  intro N
  obtain ⟨n, hn, m, a, y, hmargin⟩ := MasulloRH.cofinal_exact_theta_gram_margin N
  let δ : ℝ := 1 / (16 * ((n : ℝ) + 1))
  let u : Fin (m + 1) → ℝ → ℂ := Fin.cons (pulse n)
    (fun i x => theta (x - (y i : ℝ)))
  let d : Fin (m + 1) → ℂ := Fin.cons 1
    (fun i => -(((a i).1 : ℂ) + ((a i).2 : ℂ) * Complex.I))
  let G : Fin (m + 1) → Fin (m + 1) → ℂ := fun i j =>
    ∫ x : ℝ,
      (Real.exp (2 * (3 / 4) * x + 2 * (1 / 4 - δ) * |x|) : ℂ) *
        conj (u i x) * u j x
  have hG : (∑ i, ∑ j, conj (d i) * d j * G i j).re < δ / 2 := hmargin
  obtain ⟨R, η, hη, hentry, hcertificate⟩ :=
    MasulloRH.finite_rational_complex_gram_certificate d G (δ / 2) hG
  exact ⟨n, hn, m, a, y, R, η, hη, hentry, hcertificate⟩

end

-- Step 4: `MasulloRH.cofinal_rational_theta_gram_interval_tables` implies `MasulloRH.cofinal_rational_theta_gram_certificates` (accepted reduction of `MasulloRH.cofinal_rational_theta_gram_certificates`).
section

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

end

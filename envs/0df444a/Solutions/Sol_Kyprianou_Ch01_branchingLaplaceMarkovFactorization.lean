-- Prove2me | solution 1 for Kyprianou.Ch01.branchingLaplaceMarkovFactorization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:36:59.816404+00:00
-- url     : https://prove2.me/submissions/a2e9fa13-891f-448e-830a-aa2e89c6d49c

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingLaplaceExponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

private theorem pmf_laplace_bind_enn (p : PMF ℕ)
    (q : ℕ → PMF ℕ) (w : ℕ → ENNReal) :
    (∑' n : ℕ, (p.bind q n) * w n) =
      ∑' k : ℕ, p k * (∑' n : ℕ, q k n * w n) := by
  simp only [PMF.bind_apply]
  calc
    (∑' n : ℕ, (∑' k : ℕ, p k * q k n) * w n) =
      ∑' n : ℕ, ∑' k : ℕ, (p k * q k n) * w n := by
        apply tsum_congr
        intro n
        rw [ENNReal.tsum_mul_right]
    _ = ∑' k : ℕ, ∑' n : ℕ, (p k * q k n) * w n :=
      ENNReal.tsum_comm
    _ = ∑' k : ℕ, p k * (∑' n : ℕ, q k n * w n) := by
      apply tsum_congr
      intro k
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro n
      ring

private theorem pmf_laplace_bind_real (p : PMF ℕ)
    (q : ℕ → PMF ℕ) (phi : ℝ) (hphi : 0 < phi) :
    (∑' n : ℕ, ((p.bind q) n).toReal * Real.exp (-phi * (n : ℝ))) =
      ∑' k : ℕ, (p k).toReal *
        (∑' n : ℕ, (q k n).toReal * Real.exp (-phi * (n : ℝ))) := by
  let w : ℕ → ENNReal := fun n => ENNReal.ofReal (Real.exp (-phi * (n : ℝ)))
  have hw : ∀ n, w n ≤ 1 := by
    intro n
    dsimp [w]
    apply ENNReal.ofReal_le_one.mpr
    have hnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hfinite (r : PMF ℕ) (n : ℕ) : r n * w n ≠ ⊤ :=
    ENNReal.mul_ne_top (r.apply_ne_top n) (by simp [w])
  have hinner_le (k : ℕ) : (∑' n : ℕ, q k n * w n) ≤ 1 := by
    calc
      (∑' n : ℕ, q k n * w n) ≤ ∑' n : ℕ, q k n := by
        apply ENNReal.tsum_le_tsum
        intro n
        simpa using
          (mul_le_mul_of_nonneg_left (hw n) (show 0 ≤ q k n from zero_le))
      _ = 1 := PMF.tsum_coe (q k)
  have hinner_finite (k : ℕ) :
      (∑' n : ℕ, q k n * w n) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (hinner_le k) ENNReal.one_lt_top)
  have hinnerCast (r : PMF ℕ) :
      (∑' n : ℕ, r n * w n).toReal =
        ∑' n : ℕ, (r n).toReal * Real.exp (-phi * (n : ℝ)) := by
    rw [ENNReal.tsum_toReal_eq (hfinite r)]
    apply tsum_congr
    intro n
    rw [ENNReal.toReal_mul]
    simp [w, (Real.exp_pos _).le]
  have houtFinite (k : ℕ) :
      p k * (∑' n : ℕ, q k n * w n) ≠ ⊤ :=
    ENNReal.mul_ne_top (p.apply_ne_top k) (hinner_finite k)
  have h := congrArg ENNReal.toReal (pmf_laplace_bind_enn p q w)
  rw [hinnerCast (p.bind q)] at h
  rw [ENNReal.tsum_toReal_eq houtFinite] at h
  convert h using 1
  apply tsum_congr
  intro k
  rw [ENNReal.toReal_mul]
  rw [hinnerCast (q k)]

theorem solution
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hmarkov : IsPopulationMarkovSemigroup law)
    (hzero : ∀ t : ℝ≥0, law 0 t = PMF.pure 0)
    (hpositive : ∀ t : ℝ≥0, ∀ phi : ℝ, 0 < phi →
      0 < branchingLaplace law 1 t phi ∧
        branchingLaplace law 1 t phi < 1) :
    ∀ (s t : ℝ≥0) (phi : ℝ), 0 < phi →
      branchingLaplace law 1 (s + t) phi =
        branchingLaplace law 1 s (branchingU law t phi) := by
  intro s t phi hphi
  have hconv := pmf_laplace_bind_real
    (law 1 s) (fun k => law k t) phi hphi
  calc
    branchingLaplace law 1 (s + t) phi =
      ∑' k : ℕ, (law 1 s k).toReal * branchingLaplace law k t phi := by
        unfold branchingLaplace
        rw [hmarkov 1 s t]
        simpa only [branchingLaplace] using hconv
    _ = ∑' k : ℕ,
        (law 1 s k).toReal *
          Real.exp (-(k : ℝ) * branchingU law t phi) := by
      apply tsum_congr
      intro k
      rw [Kyprianou.Ch01.branchingLaplaceExponential
        law hbranch hzero (fun t phi hphi => (hpositive t phi hphi).1)
        k t phi hphi]
    _ = branchingLaplace law 1 s (branchingU law t phi) := by
      unfold branchingLaplace
      apply tsum_congr
      intro n
      congr 1
      ring

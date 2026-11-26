-- Prove2me | solution 1 for MasulloRH.signed_translate_energy_upper_of_grid_enclosures
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T09:22:33.939237+00:00
-- url     : https://prove2.me/submissions/bb3a4096-e1ae-4b6d-a215-f426aec4b656

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped BigOperators

theorem solution {m : ℕ} (J : ℕ) (L h : ℝ) (hh : 0 ≤ h)
    (p t : ℝ → ℂ) (w : ℝ → ℝ) (a : Fin m → ℂ) (s : Fin m → ℤ)
    (P : ℕ → ℂ) (R W : ℕ → ℝ) (T : ℤ → ℂ) (U : ℤ → ℝ) :
    let e (k : ℤ) := L + (k : ℝ) * h
    let F (x : ℝ) := w x * ‖p x - ∑ i, a i * t (x - (s i : ℝ) * h)‖ ^ 2
    let A (j : ℕ) := ‖P j - ∑ i, a i * T ((j : ℤ) - s i)‖ +
      (R j + ∑ i, ‖a i‖ * U ((j : ℤ) - s i))
    Integrable F →
    (∀ j < J, 0 ≤ W j ∧ ∀ x ∈ Icc (e j) (e ((j : ℤ) + 1)),
      ‖p x - P j‖ ≤ R j ∧ w x ≤ W j) →
    (∀ j < J, ∀ i : Fin m, ∀ z ∈ Icc (e ((j : ℤ) - s i)) (e ((j : ℤ) - s i + 1)),
      ‖t z - T ((j : ℤ) - s i)‖ ≤ U ((j : ℤ) - s i)) →
    (∫ x : ℝ in Icc L (e J), F x) ≤
      ∑ j ∈ Finset.range J, h * (W j * A j ^ 2) := by
  classical
  intro e F A hf hp ht
  let edge (j : ℕ) := e j
  have hedge (j : ℕ) : edge (j+1) = edge j + h := by
    simp [edge,e,add_mul]
    ring
  have hmono (j : ℕ) : edge j ≤ edge (j+1) := by rw [hedge]; linarith
  have hstep (j : ℕ) : edge (j+1) = e ((j : ℤ)+1) := by simp [edge]
  have h0 : edge 0 = L := by simp [edge,e]
  have hN : edge 0 ≤ edge J := by
    simp [edge, e]
    positivity
  have hequiv (j : ℕ) (hj : j < J) (x : ℝ) (hx : x ∈ Icc (edge j) (edge (j+1))) :
      F x ≤ W j * A j ^ 2 := by
    have hxx := hx
    rw [hstep] at hxx
    have hpc := (hp j hj).2 x hxx
    have hs (i : Fin m) : ‖t (x - (s i : ℝ)*h) - T ((j : ℤ)-s i)‖ ≤ U ((j : ℤ)-s i) := by
      apply ht j hj i
      rcases hxx with ⟨hl,hr⟩
      change L + (((j : ℤ)-s i : ℤ) : ℝ)*h ≤ _ ∧ _ ≤ L + (((j : ℤ)-s i+1 : ℤ) : ℝ)*h
      simp only [edge,e,Int.cast_add,Int.cast_sub,Int.cast_natCast,Int.cast_one] at hl hr ⊢
      constructor <;> nlinarith
    have herr : ‖∑ i, a i * (t (x - (s i : ℝ)*h) - T ((j : ℤ)-s i))‖ ≤
        ∑ i, ‖a i‖ * U ((j : ℤ)-s i) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hs i) (norm_nonneg _)
    have eqn : p x - ∑ i, a i * t (x-(s i : ℝ)*h) =
        (P j - ∑ i, a i * T ((j : ℤ)-s i)) +
          ((p x-P j) - ∑ i, a i*(t (x-(s i : ℝ)*h) - T ((j : ℤ)-s i))) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      abel
    have hn : ‖p x - ∑ i, a i * t (x-(s i : ℝ)*h)‖ ≤ A j := by
      rw [eqn]
      exact (norm_add_le _ _).trans (add_le_add le_rfl
        ((norm_sub_le _ _).trans (add_le_add hpc.1 herr)))
    apply (mul_le_mul_of_nonneg_right hpc.2 (sq_nonneg _)).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) (hp j hj).1
  rw [← h0, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hN]
  change (∫ x in edge 0..edge J, F x) ≤ _
  rw [← intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hf.intervalIntegrable)]
  apply Finset.sum_le_sum
  intro j hj
  calc
    (∫ x in edge j..edge (j+1), F x) ≤ ∫ _ in edge j..edge (j+1), W j * A j ^ 2 :=
      intervalIntegral.integral_mono_on (hmono j) hf.intervalIntegrable intervalIntegrable_const
        (hequiv j (Finset.mem_range.mp hj))
    _ = _ := by rw [intervalIntegral.integral_const, hedge]; simp

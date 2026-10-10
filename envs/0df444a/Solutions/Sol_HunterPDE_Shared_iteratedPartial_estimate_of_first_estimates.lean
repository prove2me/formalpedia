-- Prove2me | solution 1 for HunterPDE.Shared.iteratedPartial_estimate_of_first_estimates
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T15:25:56.84538+00:00
-- url     : https://prove2.me/submissions/d8083111-e64a-4581-bd8f-61aa16f583c7

import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open HunterPDE.Shared Metric
set_option autoImplicit false

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hfirst : ∀ (l : List (Fin n)) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ),
      0 < r → closedBall x r ⊆ Ω → ∀ (i : Fin n) (M : ℝ),
      (∀ y ∈ closedBall x r, |iteratedPartial u l y| ≤ M) →
      |partialDeriv (iteratedPartial u l) i x| ≤ (n / r) * M)
    (l : List (Fin n)) (hl : 1 ≤ l.length)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hball : closedBall x r ⊆ Ω) {M : ℝ}
    (hM : ∀ y ∈ closedBall x r, |u y| ≤ M) :
    |iteratedPartial u l x| ≤
      ((n : ℝ) ^ l.length * Real.exp 1 ^ (l.length - 1) *
        (l.length.factorial : ℝ) / r ^ l.length) * M := by
  induction l generalizing x r M with
  | nil => simp at hl
  | cons i l ih =>
    cases l with
    | nil =>
      simpa [iteratedPartial] using hfirst [] x r hr hball i M hM
    | cons j t =>
      let k := (j :: t).length
      have hk : 1 ≤ k := by simp [k]
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
      have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
      have hkp : (0 : ℝ) < k + 1 := by positivity
      have hkpne : (k : ℝ) + 1 ≠ 0 := ne_of_gt hkp
      let ρ := r / ((k : ℝ) + 1)
      let s := r * (k : ℝ) / ((k : ℝ) + 1)
      have hρ : 0 < ρ := by dsimp [ρ]; positivity
      have hs : 0 < s := by dsimp [s]; positivity
      have hrs : s + ρ = r := by dsimp [s, ρ]; field_simp
      have hρr : ρ ≤ r := by linarith
      have hsmall : closedBall x ρ ⊆ Ω :=
        fun y hy => hball (closedBall_subset_closedBall hρr hy)
      have hM0 : 0 ≤ M := (abs_nonneg (u x)).trans (hM x (mem_closedBall_self hr.le))
      have hinner : ∀ y ∈ closedBall x ρ, |iteratedPartial u (j :: t) y| ≤
          ((n : ℝ) ^ k * Real.exp 1 ^ (k - 1) * (k.factorial : ℝ) / s ^ k) * M := by
        intro y hy
        have hsub : closedBall y s ⊆ closedBall x r := by
          intro z hz
          apply mem_closedBall.mpr
          calc
            dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
            _ ≤ s + ρ := add_le_add (mem_closedBall.mp hz) (mem_closedBall.mp hy)
            _ = r := hrs
        exact ih (by simp) hs (hsub.trans hball) (fun z hz => hM z (hsub hz))
      have hstep := hfirst (j :: t) x ρ hρ hsmall i
        (((n : ℝ) ^ k * Real.exp 1 ^ (k - 1) * (k.factorial : ℝ) / s ^ k) * M) hinner
      have hsplit : ((k : ℝ) + 1) ^ k / (k : ℝ) ^ k ≤ Real.exp 1 := by
        rw [← div_pow]
        convert Real.one_add_inv_pow_le_exp (n := k) using 1
        congr 1
        field_simp
      have hcoeff : (n : ℝ) / ρ *
          ((n : ℝ) ^ k * Real.exp 1 ^ (k - 1) * (k.factorial : ℝ) / s ^ k) ≤
          (n : ℝ) ^ (k + 1) * Real.exp 1 ^ k * ((k + 1).factorial : ℝ) / r ^ (k + 1) := by
        have hpow : Real.exp 1 ^ k = Real.exp 1 ^ (k - 1) * Real.exp 1 := by
          nth_rw 1 [← Nat.sub_add_cancel hk]
          rw [pow_succ]
        have heq : (n : ℝ) / ρ *
            ((n : ℝ) ^ k * Real.exp 1 ^ (k - 1) * (k.factorial : ℝ) / s ^ k) =
            ((n : ℝ) ^ (k + 1) * Real.exp 1 ^ (k - 1) *
              ((k + 1).factorial : ℝ) / r ^ (k + 1)) *
              (((k : ℝ) + 1) ^ k / (k : ℝ) ^ k) := by
          dsimp [ρ, s]
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
            div_pow, mul_pow]
          simp only [pow_succ]
          field_simp [hkne, hkpne, ne_of_gt hr]
        rw [heq, hpow]
        calc
          _ ≤ ((n : ℝ) ^ (k + 1) * Real.exp 1 ^ (k - 1) *
              ((k + 1).factorial : ℝ) / r ^ (k + 1)) * Real.exp 1 :=
            mul_le_mul_of_nonneg_left hsplit (by positivity)
          _ = _ := by ring
      change |partialDeriv (iteratedPartial u (j :: t)) i x| ≤ _
      calc
        _ ≤ (n / ρ) *
            (((n : ℝ) ^ k * Real.exp 1 ^ (k - 1) * (k.factorial : ℝ) / s ^ k) * M) := hstep
        _ = ((n / ρ) *
            ((n : ℝ) ^ k * Real.exp 1 ^ (k - 1) * (k.factorial : ℝ) / s ^ k)) * M := by ring
        _ ≤ ((n : ℝ) ^ (k + 1) * Real.exp 1 ^ k * ((k + 1).factorial : ℝ) /
            r ^ (k + 1)) * M := mul_le_mul_of_nonneg_right hcoeff hM0
        _ = _ := by simp [k]

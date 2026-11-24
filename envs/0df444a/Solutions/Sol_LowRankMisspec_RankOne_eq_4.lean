-- Prove2me | solution 1 for LowRankMisspec.RankOne.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:59:47.580999+00:00
-- url     : https://prove2.me/submissions/8b35e49a-b80f-4909-bc9b-35485cfc0b9f

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws

set_option autoImplicit false

open LowRankMisspec.RankOne

private lemma prodLaw_nonneg {σ T : ℕ} (p : Fin T → Fin σ → ℝ) (hp : ∀ t, IsLaw (p t))
    (x : Fin T → Fin σ) : 0 ≤ prodLaw p x :=
  Finset.prod_nonneg fun t _ => (hp t).1 (x t)

private lemma prodLaw_sum {σ T : ℕ} (p : Fin T → Fin σ → ℝ) (hp : ∀ t, IsLaw (p t)) :
    ∑ x, prodLaw p x = 1 := by
  unfold prodLaw
  rw [← Fintype.prod_sum (fun t a => p t a)]
  exact Finset.prod_eq_one fun t _ => (hp t).2

private lemma prodLaw_succ {σ T : ℕ} (p : Fin (T + 1) → Fin σ → ℝ) (a : Fin σ)
    (y : Fin T → Fin σ) :
    prodLaw p (Fin.cons a y) = p 0 a * prodLaw (fun i => p i.succ) y := by
  unfold prodLaw
  rw [Fin.prod_univ_succ]
  simp

private lemma sum_succ {σ T : ℕ} (f : (Fin (T + 1) → Fin σ) → ℝ) :
    ∑ x, f x = ∑ a : Fin σ, ∑ y : Fin T → Fin σ, f (Fin.cons a y) := by
  rw [← (Fin.consEquiv fun _ : Fin (T + 1) => Fin σ).sum_comp, Fintype.sum_prod_type]
  rfl

theorem solution {σ T : ℕ} (p r : Fin T → Fin σ → ℝ) (hp : ∀ t, IsLaw (p t))
    (hr : ∀ t, IsLaw (r t)) :
    l1 (prodLaw p) (prodLaw r) ≤ ∑ t, l1 (p t) (r t) := by
  induction T with
  | zero => simp [l1, prodLaw]
  | succ T ih =>
    set P := prodLaw (fun i : Fin T => p i.succ)
    set R := prodLaw (fun i : Fin T => r i.succ)
    have hP : ∑ y, P y = 1 := prodLaw_sum (fun i : Fin T => p i.succ) (fun i => hp i.succ)
    have hPn : ∀ y, 0 ≤ P y := prodLaw_nonneg (fun i : Fin T => p i.succ) (fun i => hp i.succ)
    have hIH := ih (fun i => p i.succ) (fun i => r i.succ) (fun i => hp i.succ)
      (fun i => hr i.succ)
    have hr0 := hr 0
    have key : ∀ a y, |prodLaw p (Fin.cons a y) - prodLaw r (Fin.cons a y)| ≤
        |p 0 a - r 0 a| * P y + r 0 a * |P y - R y| := by
      intro a y
      rw [prodLaw_succ, prodLaw_succ]
      have e : p 0 a * P y - r 0 a * R y = (p 0 a - r 0 a) * P y + r 0 a * (P y - R y) := by
        ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hPn y), abs_of_nonneg (hr0.1 a)]
    calc l1 (prodLaw p) (prodLaw r)
        = ∑ a : Fin σ, ∑ y : Fin T → Fin σ,
            |prodLaw p (Fin.cons a y) - prodLaw r (Fin.cons a y)| := by
          unfold l1; exact sum_succ _
      _ ≤ ∑ a : Fin σ, ∑ y : Fin T → Fin σ, (|p 0 a - r 0 a| * P y + r 0 a * |P y - R y|) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun y _ => key a y
      _ = l1 (p 0) (r 0) + l1 P R := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hP, mul_one, ← Finset.sum_mul,
            hr0.2, one_mul]
          rfl
      _ ≤ l1 (p 0) (r 0) + ∑ i : Fin T, l1 (p i.succ) (r i.succ) := by linarith
      _ = ∑ t, l1 (p t) (r t) := (Fin.sum_univ_succ (fun t => l1 (p t) (r t))).symm

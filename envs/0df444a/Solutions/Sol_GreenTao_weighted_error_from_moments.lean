-- Prove2me | solution 1 for GreenTao.weighted_error_from_moments
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:17:53.045827+00:00
-- url     : https://prove2.me/submissions/182b791b-a9dd-4772-a1f3-2419ae98e592

import Definitions.Def_GreenTao_Pseudorandom
import Mathlib

open scoped BigOperators Topology
open Filter GreenTao

private lemma avg_mono_mom {α : Type} [Fintype α] {f g : α → ℝ}
    (h : ∀ x, f x ≤ g x) : avg f ≤ avg g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

private lemma avg_nonneg_mom {α : Type} [Fintype α] {f : α → ℝ}
    (h : ∀ x, 0 ≤ f x) : 0 ≤ avg f := by
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => h x)

private lemma avg_abs_mom {α : Type} [Fintype α] (f : α → ℝ) :
    |avg f| ≤ avg (fun x => |f x|) := by
  simp only [avg, abs_mul, abs_of_nonneg (show 0 ≤ (Fintype.card α : ℝ)⁻¹ by positivity)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

theorem solution (A : ℕ → Type) [∀ n, Fintype (A n)]
    (V W : ∀ n, A n → ℝ) (hV : ∀ n x, 0 ≤ V n x)
    (h₀ : Tendsto (fun n => avg (V n)) atTop (𝓝 1))
    (h₁ : Tendsto (fun n => avg (fun x => W n x * V n x)) atTop (𝓝 1))
    (h₂ : Tendsto (fun n => avg (fun x => W n x ^ 2 * V n x)) atTop (𝓝 1)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      ∀ H : A n → ℝ, (∀ x, |H x| ≤ V n x) →
        |avg (fun x => (W n x - 1) * H x)| ≤ η := by
  classical
  let E : ℕ → ℝ := fun n => avg (fun x => |W n x - 1| * V n x)
  let Q : ℕ → ℝ := fun n => avg (fun x => (W n x - 1) ^ 2 * V n x)
  have hQ : Tendsto Q atTop (𝓝 0) := by
    have heq (n) : Q n =
        avg (fun x => W n x ^ 2 * V n x) - 2 * avg (fun x => W n x * V n x) + avg (V n) := by
      have hp (x : A n) : (W n x - 1) ^ 2 * V n x =
          W n x ^ 2 * V n x - 2 * (W n x * V n x) + V n x := by ring
      dsimp [Q]
      simp_rw [hp]
      simp only [avg, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    have hh := (h₂.sub (h₁.const_mul 2)).add h₀
    simp only [show (1 : ℝ) - 2 * 1 + 1 = 0 by norm_num] at hh
    exact hh.congr' (Eventually.of_forall fun n => (heq n).symm)
  have hcs (n) : (E n) ^ 2 ≤ avg (V n) * Q n := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (s := (Finset.univ : Finset (A n)))
      (r := fun x => |W n x - 1| * V n x) (f := V n)
      (g := fun x => (W n x - 1) ^ 2 * V n x)
      (fun x _ => hV n x) (fun x _ => mul_nonneg (sq_nonneg _) (hV n x))
      (fun x _ => by rw [mul_pow, sq_abs]; ring_nf; rfl)
    have hscale := mul_le_mul_of_nonneg_left h (sq_nonneg ((Fintype.card (A n) : ℝ)⁻¹))
    simpa only [E, Q, avg, mul_pow, pow_two, mul_assoc, mul_left_comm, mul_comm] using hscale
  have hlim : Tendsto (fun n => (E n) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg (E n)) hcs
    simpa using h₀.mul hQ
  intro η hη
  have hevent : ∀ᶠ n in atTop, (E n) ^ 2 < η ^ 2 :=
    (tendsto_order.mp hlim).2 _ (sq_pos_of_pos hη)
  filter_upwards [hevent] with n hn
  intro H hH
  have hEH : |avg (fun x => (W n x - 1) * H x)| ≤ E n := by
    apply (avg_abs_mom _).trans
    apply avg_mono_mom
    intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hH x) (abs_nonneg _)
  have hEpos : 0 ≤ E n := avg_nonneg_mom (fun x => mul_nonneg (abs_nonneg _) (hV n x))
  have hsmall : E n ≤ η := by nlinarith
  exact hEH.trans hsmall

-- Prove2me | solution 1 for MurtyKabadi.Reduction.problem9_special_case_problem4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:03:13.062642+00:00
-- url     : https://prove2.me/submissions/af9f865a-99d5-4897-8959-8a6257faa010

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems
import Definitions.Def_MurtyKabadi_Reduction_Construction

namespace MurtyKabadi.Reduction

open Matrix

theorem aux_p9p4_inner (n : ℕ) (a : Fin n → ℝ) (x : Fin n → ℝ) (c : ℝ) (e : Fin n → ℝ) (i : Fin n) :
    ∑ j, (a j + c + if i = j then e j else 0) * x j = ∑ j, a j * x j + c * ∑ j, x j + e i * x i := by
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum]

theorem aux_p9p4_inner' (n : ℕ) (x : Fin n → ℝ) (c e : ℝ) (i : Fin n) :
    ∑ j, (c + if i = j then e else 0) * x j = c * ∑ j, x j + e * x i := by
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum]

theorem aux_p9p4_ident {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (ε : ℚ) (y s : Fin n → ℝ) :
    f5 d d0 δ ε y s = Q (mkMatrix d d0 δ ε) (Sum.elim y s) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((d0 : ℝ) ^ 2 - n * δ - ε) / (n : ℝ) ^ 2 := ⟨_, rfl⟩
  have h1 : Q (mkMatrix d d0 δ ε) (Sum.elim y s) =
      ∑ i, y i * (∑ j, ((d i : ℝ) * d j + c + if i = j then (δ : ℝ) - 2 * d0 * d j else 0) * y j
        + ∑ j, (c + if i = j then (δ : ℝ) + 1 / 2 else 0) * s j)
      + ∑ i, s i * (∑ j, (c + if i = j then (δ : ℝ) + 1 / 2 else 0) * y j
        + ∑ j, (c + if i = j then (δ : ℝ) else 0) * s j) := by
    simp only [Q, dotProduct, mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mkMatrix]
    subst hc
    rfl
  rw [h1]
  simp only [aux_p9p4_inner, aux_p9p4_inner']
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ j, (d j : ℝ) * y j := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = ∑ j, y j := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ j, s j := ⟨_, rfl⟩
  have e1 : ∀ i, ∑ j, (d i : ℝ) * d j * y j = d i * A := by
    intro i; rw [hA, Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
  simp only [e1, ← hY, ← hS]
  have e2 : ∑ i, y i * (d i * A + c * Y + ((δ : ℝ) - 2 * d0 * d i) * y i + (c * S + ((δ : ℝ) + 1 / 2) * s i))
      = A * A + c * Y * Y + δ * ∑ i, y i ^ 2 - 2 * d0 * ∑ i, (d i : ℝ) * y i ^ 2 + c * S * Y
        + (δ + 1 / 2) * ∑ i, y i * s i := by
    have : ∀ i, y i * (d i * A + c * Y + ((δ : ℝ) - 2 * d0 * d i) * y i + (c * S + ((δ : ℝ) + 1 / 2) * s i))
        = A * (d i * y i) + (c * Y) * y i + δ * y i ^ 2 - 2 * d0 * (d i * y i ^ 2) + (c * S) * y i
          + (δ + 1 / 2) * (y i * s i) := fun i => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hA, ← hY]
  have e3 : ∑ i, s i * (c * Y + ((δ : ℝ) + 1 / 2) * y i + (c * S + (δ : ℝ) * s i))
      = c * Y * S + (δ + 1 / 2) * ∑ i, y i * s i + c * S * S + δ * ∑ i, s i ^ 2 := by
    have : ∀ i, s i * (c * Y + ((δ : ℝ) + 1 / 2) * y i + (c * S + (δ : ℝ) * s i))
        = (c * Y) * s i + (δ + 1 / 2) * (y i * s i) + (c * S) * s i + δ * s i ^ 2 := fun i => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← hS]
  rw [e2, e3]
  have e4 : ∑ j, (y j + s j) = Y + S := by rw [hY, hS]; exact Finset.sum_add_distrib
  have e5 : ∑ j, (y j + s j) ^ 2 = ∑ j, y j ^ 2 + 2 * ∑ j, y j * s j + ∑ j, s j ^ 2 := by
    have : ∀ j, (y j + s j) ^ 2 = y j ^ 2 + 2 * (y j * s j) + s j ^ 2 := fun j => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [f5, f4, e4, e5, ← hA]
  rw [hc]
  ring

end MurtyKabadi.Reduction

open MurtyKabadi.Reduction

theorem solution {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (ε : ℚ) :
    (∀ y s : Fin n → ℝ, f5 d d0 δ ε y s = Q (mkMatrix d d0 δ ε) (Sum.elim y s)) ∧
    ((∃ p ∈ P n, f5 d d0 δ ε p.1 p.2 < 0) ↔ Problem4 (mkMatrix d d0 δ ε) n) := by
  refine ⟨fun y s => aux_p9p4_ident d d0 δ ε y s, ?_⟩
  constructor
  · rintro ⟨⟨y, s⟩, ⟨hy, hs, hsum⟩, hneg⟩
    refine ⟨Sum.elim y s, ?_, ?_, ?_⟩
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← Finset.sum_add_distrib]
      exact hsum
    · intro a
      cases a with
      | inl i => exact hy i
      | inr i => exact hs i
    · rw [← aux_p9p4_ident]
      exact hneg
  · rintro ⟨x, hsum, hx, hneg⟩
    refine ⟨(fun i => x (Sum.inl i), fun i => x (Sum.inr i)), ⟨fun i => hx _, fun i => hx _, ?_⟩, ?_⟩
    · rw [Finset.sum_add_distrib, ← Fintype.sum_sum_type]
      exact hsum
    · rw [aux_p9p4_ident]
      have : Sum.elim (fun i => x (Sum.inl i)) (fun i => x (Sum.inr i)) = x := by
        funext a
        cases a <;> rfl
      simp only [this]
      exact hneg

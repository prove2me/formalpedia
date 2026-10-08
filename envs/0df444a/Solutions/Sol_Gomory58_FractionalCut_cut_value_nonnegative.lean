-- Prove2me | solution 1 for Gomory58.FractionalCut.cut_value_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:11:59.736312+00:00
-- url     : https://prove2.me/submissions/ff2223e3-0099-4b62-afef-77fad7587ea6

import Mathlib
import Definitions.Def_Gomory58_FractionalCut_Tableau



namespace Gomory58.FractionalCut

theorem g_drop_slack {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ) :
    (FeasibleStar a i₀ x t s → FeasibleSol a x t) ∧
    (NonnegIntSolStar a i₀ x t s → NonnegIntSol a x t) := by
  have h1 : FeasibleStar a i₀ x t s → FeasibleSol a x t := fun h =>
    ⟨h.1.1, h.2.1, h.2.2.1⟩
  exact ⟨h1, fun h => ⟨h1 h.1, h.2.1, h.2.2.1⟩⟩

theorem g_int_sum {n : ℕ} (c t : Fin n → ℝ) (hc : ∀ j, IsInt (c j)) (ht : ∀ j, IsInt (t j)) :
    IsInt (∑ j, c j * (-t j)) := by
  classical
  choose zc hzc using hc
  choose zt hzt using ht
  refine ⟨∑ j, zc j * (-zt j), ?_⟩
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hzc j, hzt j]

theorem g_frac_row {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1) → ℝ) (i₀ : Fin (m + 1))
    (hconst : Int.fract (a i₀ 0) ≠ 0)
    (hcoeff : ∀ j : Fin n, Int.fract (a i₀ j.succ) = 0) :
    ¬ ∃ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ),
      TableauSol a x t ∧ IsInt (x i₀) ∧ (∀ j, IsInt (t j)) := by
  rintro ⟨x, t, hs, ⟨z, hz⟩, ht⟩
  have hc : ∀ j : Fin n, IsInt (a i₀ j.succ) := fun j => by
    have := hcoeff j
    rw [Int.fract, sub_eq_zero] at this
    exact ⟨⌊a i₀ j.succ⌋, this.symm⟩
  obtain ⟨w, hw⟩ := g_int_sum (fun j => a i₀ j.succ) t hc ht
  apply hconst
  have h := hs i₀
  have : a i₀ 0 = ((z - w : ℤ) : ℝ) := by
    push_cast; rw [hz, hw]; linarith
  rw [this]; simp

theorem g_cut_integral {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ)
    (hsol : TableauSol a x t) (hx : IsInt (x i₀)) (ht : ∀ j, IsInt (t j)) :
    cutValue a i₀ t =
      ((Int.floor (a i₀ 0) : ℝ) +
        (∑ j : Fin n, (Int.floor (a i₀ j.succ) : ℝ) * (-t j)) - x i₀) ∧
    IsInt (cutValue a i₀ t) := by
  have heq : cutValue a i₀ t =
      ((Int.floor (a i₀ 0) : ℝ) +
        (∑ j : Fin n, (Int.floor (a i₀ j.succ) : ℝ) * (-t j)) - x i₀) := by
    have h := hsol i₀
    unfold cutValue
    have e : ∑ j : Fin n, a i₀ j.succ * (-t j) =
        ∑ j : Fin n, (Int.floor (a i₀ j.succ) : ℝ) * (-t j) +
        ∑ j : Fin n, Int.fract (a i₀ j.succ) * (-t j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← add_mul, Int.floor_add_fract]
    have f0 := Int.floor_add_fract (a i₀ 0)
    linarith
  refine ⟨heq, ?_⟩
  rw [heq]
  obtain ⟨w, hw⟩ := g_int_sum (fun j => (Int.floor (a i₀ j.succ) : ℝ)) t
    (fun j => ⟨_, rfl⟩) ht
  obtain ⟨z, hz⟩ := hx
  refine ⟨⌊a i₀ 0⌋ + w - z, ?_⟩
  push_cast
  rw [hw, hz]

theorem g_cut_nonneg {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ)
    (hsol : NonnegIntSol a x t) :
    -Int.fract (a i₀ 0) ≤ cutValue a i₀ t ∧ 0 ≤ cutValue a i₀ t := by
  have h1 : -Int.fract (a i₀ 0) ≤ cutValue a i₀ t := by
    unfold cutValue
    have : 0 ≤ ∑ j : Fin n, Int.fract (a i₀ j.succ) * t j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (Int.fract_nonneg _) (hsol.1.2.2 j)
    have e : ∑ j : Fin n, Int.fract (a i₀ j.succ) * (-t j) =
        -∑ j : Fin n, Int.fract (a i₀ j.succ) * t j := by
      rw [← Finset.sum_neg_distrib]; simp
    linarith
  refine ⟨h1, ?_⟩
  obtain ⟨_, ⟨z, hz⟩⟩ := g_cut_integral a i₀ x t hsol.1.1 (hsol.2.1 i₀) hsol.2.2
  rw [← hz] at h1 ⊢
  have hf := Int.fract_lt_one (a i₀ 0)
  have : (-1 : ℝ) < z := by linarith
  have : (-1 : ℤ) < z := by exact_mod_cast this
  exact_mod_cast (by omega : (0:ℤ) ≤ z)

theorem g_goal {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1) → ℝ) (i₀ : Fin (m + 1))
    (h : ¬ IsInt (a i₀ 0)) :
    TableauSol a (fun i => a i 0) (fun _ => 0) ∧
    cutValue a i₀ (fun _ => 0) = -Int.fract (a i₀ 0) ∧
    ¬ FeasibleStar a i₀ (fun i => a i 0) (fun _ => 0)
      (cutValue a i₀ (fun _ => 0)) ∧
    (∀ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ),
      NonnegIntSol a x t ↔ NonnegIntSolStar a i₀ x t (cutValue a i₀ t)) ∧
    (∀ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ),
      NonnegIntSolStar a i₀ x t s → s = cutValue a i₀ t) ∧
    (∀ W : ℝ,
      IsGreatest {v : ℝ | ∃ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ),
        NonnegIntSol a x t ∧ x 0 = v} W ↔
      IsGreatest {v : ℝ | ∃ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ),
        NonnegIntSolStar a i₀ x t s ∧ x 0 = v} W) := by
  have hT : TableauSol a (fun i => a i 0) (fun _ => 0) := fun i => by simp
  have hc : cutValue a i₀ (fun _ => 0) = -Int.fract (a i₀ 0) := by simp [cutValue]
  have hf : Int.fract (a i₀ 0) ≠ 0 := fun h0 => by
    apply h
    rw [Int.fract, sub_eq_zero] at h0
    exact ⟨_, h0.symm⟩
  have hpos : 0 < Int.fract (a i₀ 0) := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hf)
  have h4 : ∀ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ),
      NonnegIntSol a x t ↔ NonnegIntSolStar a i₀ x t (cutValue a i₀ t) := by
    intro x t
    constructor
    · intro hs
      obtain ⟨hv, hz⟩ := g_cut_nonneg a i₀ x t hs
      exact ⟨⟨⟨hs.1.1, rfl⟩, hs.1.2.1, hs.1.2.2, hz⟩, hs.2.1, hs.2.2,
        (g_cut_integral a i₀ x t hs.1.1 (hs.2.1 i₀) hs.2.2).2⟩
    · intro hs
      exact (g_drop_slack a i₀ x t _).2 hs
  have h5 : ∀ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ),
      NonnegIntSolStar a i₀ x t s → s = cutValue a i₀ t := fun x t s hs => hs.1.1.2
  refine ⟨hT, hc, ?_, h4, h5, ?_⟩
  · intro hF
    have := hF.2.2.2
    rw [hc] at this
    linarith
  · intro W
    have hset : {v : ℝ | ∃ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ),
        NonnegIntSol a x t ∧ x 0 = v} = {v : ℝ | ∃ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ),
        NonnegIntSolStar a i₀ x t s ∧ x 0 = v} := by
      ext v
      constructor
      · rintro ⟨x, t, hs, hv⟩
        exact ⟨x, t, _, (h4 x t).1 hs, hv⟩
      · rintro ⟨x, t, s, hs, hv⟩
        have := h5 x t s hs
        subst this
        exact ⟨x, t, (h4 x t).2 hs, hv⟩
    rw [hset]

end Gomory58.FractionalCut

open Gomory58.FractionalCut


theorem solution {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ)
    (hsol : NonnegIntSol a x t) :
    -Int.fract (a i₀ 0) ≤ cutValue a i₀ t ∧ 0 ≤ cutValue a i₀ t := by
  exact g_cut_nonneg a i₀ x t hsol

-- Prove2me | solution 1 for KalaiKleitman92.Diameter.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:13:35.522821+00:00
-- url     : https://prove2.me/submissions/58d6c5a7-6211-4645-8de5-88688b699049

import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_ToddKK14_Diameter_base_eq
import Theorems.Thm_ToddKK14_Diameter_base_dim_one
import Theorems.Thm_KalaiKleitman92_Diameter_recursion
import Theorems.Thm_KalaiKleitman92_Diameter_bound_recursion

namespace Aux_KK92_theorem_1

open scoped RealInnerProductSpace
open Hirsch

noncomputable abbrev kkBound (d n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ (Real.logb 2 (d : ℝ) + 2)⌋₊

lemma logb_two_nat_nonneg (d : ℕ) : 0 ≤ Real.logb 2 (d : ℝ) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [Real.logb]
  · have hdR : (0 : ℝ) < (d : ℝ) := by positivity
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hdR, Real.rpow_zero]
    exact hd1

lemma kkBound_mono (d : ℕ) {m n : ℕ} (hmn : m ≤ n) : kkBound d m ≤ kkBound d n := by
  refine Nat.floor_mono ?_
  refine Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmn) ?_
  linarith [logb_two_nat_nonneg d]

lemma one_le_kkBound (d : ℕ) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ kkBound d n := by
  refine Nat.le_floor ?_
  rw [Nat.cast_one]
  refine Real.one_le_rpow (by exact_mod_cast hn) ?_
  linarith [logb_two_nat_nonneg d]

lemma walk_succ {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (L : ℕ) (u v : E)
    (h : ∃ w : ℕ → E, w 0 = u ∧ w L = v ∧ ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ w : ℕ → E, w 0 = u ∧ w (L + 1) = v ∧
      ∀ j < L + 1, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
  classical
  obtain ⟨w, h0, hL, hstep⟩ := h
  refine ⟨fun j => if j ≤ L then w j else v, by simpa using h0, by simp, ?_⟩
  intro j hj
  rcases lt_or_ge j L with h1 | h1
  · have hj1 : j + 1 ≤ L := h1
    simp only [if_pos h1.le, if_pos hj1]
    exact hstep j h1
  · have hjL : j = L := by omega
    subst hjL
    left
    simp [hL]

lemma diamLE_mono {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) {B B' : ℕ}
    (hBB : B ≤ B') (h : DiamLE P B) : DiamLE P B' := by
  intro u hu v hv
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hBB
  clear hBB
  induction m with
  | zero => simpa using h u hu v hv
  | succ m ih => exact (Nat.add_succ B m) ▸ walk_succ P (B + m) u v ih

lemma diamLE_of_n_le_d {d n : ℕ} (hnd : n ≤ d) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) : DiamLE (Hpoly a b) 0 := by
  let a' : Fin d → EuclideanSpace ℝ (Fin d) := fun j => if h : j.1 < n then a ⟨j.1, h⟩ else 0
  let b' : Fin d → ℝ := fun j => if h : j.1 < n then b ⟨j.1, h⟩ else 1
  have heq : Hpoly a b = Hpoly a' b' := by
    ext x
    constructor
    · intro hx j
      by_cases hj : j.1 < n
      · simpa [a', b', hj] using hx ⟨j.1, hj⟩
      · simp [a', b', hj]
    · intro hx i
      have hid : i.1 < d := lt_of_lt_of_le i.2 hnd
      have hxi := hx ⟨i.1, hid⟩
      simpa [a', b', i.2] using hxi
  rw [heq]
  exact ToddKK14.Diameter.base_eq d a' b'

lemma diamLE_dim_zero (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin 0)) (b : Fin n → ℝ) :
    DiamLE (Hpoly a b) 0 := by
  intro u _ v _
  have huv : u = v := by ext i; exact Fin.elim0 i
  exact ⟨fun _ => u, rfl, huv, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

lemma hpoly_eq_empty {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n)
    (hai : a i = 0) (hbi : b i < 0) : Hpoly a b = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxi := hx i
  rw [hai, inner_zero_left] at hxi
  linarith

lemma diamLE_empty {E : Type*} [AddCommGroup E] [Module ℝ E] (B : ℕ) : DiamLE (∅ : Set E) B := by
  intro u hu
  exact absurd hu.1 (by simp)

lemma hpoly_drop {d k : ℕ} (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d)) (b : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (ha : a i = 0) (hb : 0 ≤ b i) :
    Hpoly a b = Hpoly (fun j => a (i.succAbove j)) (fun j => b (i.succAbove j)) := by
  ext y
  constructor
  · intro h j
    exact h _
  · intro h j
    rcases eq_or_ne j i with rfl | hj
    · rw [ha]
      simpa using hb
    · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
      exact h j'

lemma hpoly_relax_reindex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) :
    Hpoly (fun i => if i ∈ F then a i else 0) (fun i => if i ∈ F then b i else 1)
      = Hpoly (fun j : Fin F.card => a ((F.equivFin.symm j : F) : Fin n))
              (fun j : Fin F.card => b ((F.equivFin.symm j : F) : Fin n)) := by
  ext x
  constructor
  · intro hx j
    have hmem : ((F.equivFin.symm j : F) : Fin n) ∈ F := (F.equivFin.symm j).2
    have hxj := hx ((F.equivFin.symm j : F) : Fin n)
    simpa [hmem] using hxj
  · intro hx i
    by_cases hi : i ∈ F
    · have hxi := hx (F.equivFin ⟨i, hi⟩)
      simp only [Equiv.symm_apply_apply] at hxi
      simpa [hi] using hxi
    · simp [hi]

lemma diamLE_kkBound_ind : ∀ (M d n : ℕ), d + n ≤ M →
    ∀ (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      DiamLE (Hpoly a b) (kkBound d n) := by
  intro M
  induction M with
  | zero =>
      intro d n hM a b
      have hnd : n ≤ d := by omega
      exact diamLE_mono (Hpoly a b) (Nat.zero_le _) (diamLE_of_n_le_d hnd a b)
  | succ M ih =>
      intro d n hM a b
      by_cases hnd : n ≤ d
      · exact diamLE_mono (Hpoly a b) (Nat.zero_le _) (diamLE_of_n_le_d hnd a b)
      have hdn : d < n := Nat.lt_of_not_ge hnd
      by_cases hd0 : d = 0
      · subst hd0
        exact diamLE_mono (Hpoly a b) (Nat.zero_le _) (diamLE_dim_zero n a b)
      by_cases hd1 : d = 1
      · subst hd1
        exact diamLE_mono (Hpoly a b) (one_le_kkBound 1 (by omega))
          (ToddKK14.Diameter.base_dim_one n a b)
      have hd2 : 2 ≤ d := by omega
      have hn_ge : d + 1 ≤ n := by omega
      by_cases hz : ∃ i, a i = 0
      · obtain ⟨i, hi⟩ := hz
        rcases lt_or_ge (b i) 0 with hbi | hbi
        · rw [hpoly_eq_empty a b i hi hbi]
          exact diamLE_empty _
        · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          rw [hpoly_drop a b i hi hbi]
          exact diamLE_mono _ (kkBound_mono d (Nat.le_succ k)) (ih d k (by omega) _ _)
      have hz' : ∀ i, a i ≠ 0 := fun i hi => hz ⟨i, hi⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hIH1 : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
          DiamLE (Hpoly a' b') (kkBound (d - 1) k) :=
        fun a' b' => ih (d - 1) k (by omega) a' b'
      have hIH2 : ∀ F : Finset (Fin (k + 1)), F.card ≤ (k + 1) / 2 →
          DiamLE (Hpoly (fun i => if i ∈ F then a i else 0)
            (fun i => if i ∈ F then b i else 1)) (kkBound d ((k + 1) / 2)) := by
        intro F hF
        rw [hpoly_relax_reindex a b F]
        exact diamLE_mono _ (kkBound_mono d hF) (ih d F.card (by omega) _ _)
      have hrec := KalaiKleitman92.Diameter.recursion d k a b hz'
        (kkBound (d - 1) k) (kkBound d ((k + 1) / 2)) hIH1 hIH2
      have hbnd := KalaiKleitman92.Diameter.bound_recursion d (k + 1) hd2 hn_ge
      simp only [Nat.add_sub_cancel] at hbnd
      exact diamLE_mono (Hpoly a b) hbnd hrec

end Aux_KK92_theorem_1

open scoped RealInnerProductSpace
open Hirsch

theorem solution (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    DiamLE (Hpoly a b) ⌊(n : ℝ) ^ (Real.logb 2 (d : ℝ) + 2)⌋₊ :=
  Aux_KK92_theorem_1.diamLE_kkBound_ind (d + n) d n le_rfl a b

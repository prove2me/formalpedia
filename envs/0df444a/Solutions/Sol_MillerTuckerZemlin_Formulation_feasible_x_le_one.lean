-- Prove2me | solution 1 for MillerTuckerZemlin.Formulation.feasible_x_le_one
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:53:11.012045+00:00
-- url     : https://prove2.me/submissions/a3c5d2db-b9d4-4ec7-b671-15ec535b3a38

import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model



namespace MillerTuckerZemlin.Formulation

theorem mtz_x_le_one (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) : ∀ i j : Fin (n + 1), x i j ≤ 1 := by
  obtain ⟨hd, hc, hr, -⟩ := hx
  intro i j
  by_cases hij : i = j
  · subst hij; simp [hd]
  by_cases hj : j = 0
  · subst hj
    have hi : i ≠ 0 := hij
    have h1 := hr i hi
    have h2 := Finset.single_le_sum (f := fun j => x i j) (fun _ _ => Nat.zero_le _)
      (s := Finset.univ.filter (· ≠ i)) (a := 0) (by simp [Finset.mem_filter, Ne.symm hij])
    omega
  · have h1 := hc j hj
    have h2 := Finset.single_le_sum (f := fun i => x i j) (fun _ _ => Nat.zero_le _)
      (s := Finset.univ.filter (· ≠ j)) (a := i) (by simp [Finset.mem_filter, hij])
    omega

theorem mtz_step (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) (i j : Fin (n + 1)) (hi : i ≠ 0) (hj : j ≠ 0) (h : x i j = 1) :
    u i - u j ≤ -1 := by
  have hij : i ≠ j := by
    rintro rfl
    have := hx.1 i; omega
  have := hx.2.2.2 i j hi hj hij
  rw [h] at this
  push_cast at this
  linarith

theorem mtz_path (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) (m : ℕ) (r : Fin (m + 1) → Fin (n + 1))
    (hr : ∀ k, r k ≠ 0) (hpath : ∀ k : Fin m, x (r k.castSucc) (r k.succ) = 1) :
    u (r 0) - u (r (Fin.last m)) ≤ -(m : ℝ) := by
  have key : ∀ k : ℕ, (hk : k ≤ m) → u (r 0) - u (r ⟨k, by omega⟩) ≤ -(k : ℝ) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := mtz_step n p x u hx (r ⟨k, by omega⟩) (r ⟨k+1, by omega⟩) (hr _) (hr _)
        (hpath ⟨k, by omega⟩)
      push_cast
      linarith
  have := key m le_rfl
  have e : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
  rw [e] at this
  exact this

theorem mtz_no_cycle (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ)
    (u : Fin (n + 1) → ℝ) (hx : Feasible n p x u) (k : ℕ) (r : Fin (k + 1) → Fin (n + 1))
    (hr : ∀ i, r i ≠ 0) : ¬ ∀ i : Fin (k + 1), x (r i) (r (i + 1)) = 1 := by
  intro h
  have h1 := mtz_path n p x u hx k r hr (fun i => by
    have := h i.castSucc
    rwa [Fin.coeSucc_eq_succ] at this)
  have h2 := mtz_step n p x u hx (r (Fin.last k)) (r 0) (hr _) (hr _) (by
    have := h (Fin.last k)
    rwa [Fin.last_add_one] at this)
  have : (0:ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem mtz_col_unique (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) (j i i' : Fin (n + 1)) (hj : j ≠ 0) (h : x i j = 1) (h' : x i' j = 1) :
    i = i' := by
  by_contra hne
  have hc := hx.2.1 j hj
  have hi : i ≠ j := by rintro rfl; have := hx.1 i; omega
  have hi' : i' ≠ j := by rintro rfl; have := hx.1 i'; omega
  have : x i j + x i' j ≤ ∑ a ∈ Finset.univ.filter (· ≠ j), x a j := by
    rw [← Finset.sum_pair (f := fun a => x a j) hne]
    apply Finset.sum_le_sum_of_subset
    intro a ha
    simp at ha
    simp
    rcases ha with rfl | rfl <;> assumption
  omega

theorem mtz_row_unique (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) (i j j' : Fin (n + 1)) (hi : i ≠ 0) (h : x i j = 1) (h' : x i j' = 1) :
    j = j' := by
  by_contra hne
  have hc := hx.2.2.1 i hi
  have hj : j ≠ i := by rintro rfl; have := hx.1 j; omega
  have hj' : j' ≠ i := by rintro rfl; have := hx.1 j'; omega
  have : x i j + x i j' ≤ ∑ a ∈ Finset.univ.filter (· ≠ i), x i a := by
    rw [← Finset.sum_pair (f := fun a => x i a) hne]
    apply Finset.sum_le_sum_of_subset
    intro a ha
    simp at ha
    simp
    rcases ha with rfl | rfl <;> assumption
  omega

theorem mtz_no_long (n p : ℕ) (hp : 1 ≤ p) (x : Fin (n + 1) → Fin (n + 1) → ℕ)
    (u : Fin (n + 1) → ℝ) (hx : Feasible n p x u) (r : Fin (p + 1) → Fin (n + 1))
    (hr : ∀ k, r k ≠ 0) (h0 : x 0 (r 0) = 1) :
    ¬ ∀ k : Fin p, x (r k.castSucc) (r k.succ) = 1 := by
  intro h
  have h1 := mtz_path n p x u hx p r hr h
  have hne : r (Fin.last p) ≠ r 0 := by
    intro e
    rw [e] at h1
    have : (1:ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hz : x (r (Fin.last p)) (r 0) = 0 := by
    by_contra hh
    have h1' := mtz_x_le_one n p x u hx (r (Fin.last p)) (r 0)
    have : x (r (Fin.last p)) (r 0) = 1 := by omega
    have := mtz_col_unique n p x u hx (r 0) _ _ (hr 0) this h0
    exact hr _ (by simpa using this)
  have h2 := hx.2.2.2 (r (Fin.last p)) (r 0) (hr _) (hr _) hne
  rw [hz] at h2
  have : (1:ℝ) ≤ p := by exact_mod_cast hp
  simp at h2
  linarith

end MillerTuckerZemlin.Formulation

open MillerTuckerZemlin.Formulation


theorem solution (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) : ∀ i j : Fin (n + 1), x i j ≤ 1 := by
  exact mtz_x_le_one n p x u hx

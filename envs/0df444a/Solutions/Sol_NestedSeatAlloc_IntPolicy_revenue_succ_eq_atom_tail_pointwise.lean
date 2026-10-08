-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.revenue_succ_eq_atom_tail_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:58:32.130839+00:00
-- url     : https://prove2.me/submissions/75020747-0217-4ee1-8952-c857816f72f0

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical

open NestedSeatAlloc.IntPolicy

private theorem sum_range_indicator_eq_if_le
    (n d : ℕ) (w : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1), if d = i then w i else 0) =
      if d ≤ n then w d else 0 := by
  induction n with
  | zero =>
      by_cases h : d = 0 <;> simp [Finset.sum_range_succ, h]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : d = n + 1
      · subst d
        simp [ih]
      · have hle : d ≤ n ↔ d ≤ n + 1 := by omega
        simp [ih, h, hle]

theorem solution
    {Ω : Type*} (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hint : ∀ i ω, ∃ d : ℕ, X i ω = d)
    (k n : ℕ) (hk : 0 < k) (p : ℕ → ℕ) (s : ℝ)
    (hs : s ∈ Set.Icc ((p k : ℝ) + n) ((p k : ℝ) + n + 1)) :
    ∀ ω,
      revenue f (fun j => (p j : ℝ)) (fun i => X i ω) (k + 1) s =
        (∑ i ∈ Finset.range (n + 1),
          (if X (k + 1) ω = (i : ℝ) then (i : ℝ) * f (k + 1) +
            revenue f (fun j => (p j : ℝ)) (fun i => X i ω) k (s - i)
           else 0)) +
        (if (n : ℝ) < X (k + 1) ω then
          (s - (p k : ℝ)) * f (k + 1) +
            revenue f (fun j => (p j : ℝ)) (fun i => X i ω) k (p k : ℝ)
         else 0) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  intro ω
  obtain ⟨d, hd⟩ := hint (j + 2) ω
  have hreslo : (n : ℝ) ≤ s - (p (j + 1) : ℝ) := by
    have := hs.1
    linarith
  have hreshi : s - (p (j + 1) : ℝ) ≤ (n : ℝ) + 1 := by
    have := hs.2
    linarith
  have hsum := sum_range_indicator_eq_if_le n d
    (fun i => (i : ℝ) * f (j + 2) +
      revenue f (fun q => (p q : ℝ)) (fun q => X q ω) (j + 1)
        (s - i))
  have hsumEq :
      (∑ i ∈ Finset.range (n + 1),
        (if X (j + 2) ω = (i : ℝ) then
          (i : ℝ) * f (j + 2) +
            revenue f (fun q => (p q : ℝ)) (fun q => X q ω) (j + 1)
              (s - i)
         else 0)) =
        if d ≤ n then
          (d : ℝ) * f (j + 2) +
            revenue f (fun q => (p q : ℝ)) (fun q => X q ω) (j + 1)
              (s - d)
        else 0 := by
    simpa [hd] using hsum
  by_cases hdn : d ≤ n
  · have hdR : (d : ℝ) ≤ n := by exact_mod_cast hdn
    have hseat : (p (j + 1) : ℝ) ≤ s := by linarith
    have hseatD : (p (j + 1) : ℝ) + (d : ℝ) ≤ s := by linarith
    have hmiddle : ¬ s < (p (j + 1) : ℝ) + X (j + 2) ω := by
      rw [hd]
      exact not_lt_of_ge hseatD
    have hmiddleD : ¬ s < (p (j + 1) : ℝ) + (d : ℝ) := by
      simpa [hd] using hmiddle
    have htail : ¬ (n : ℝ) < X (j + 2) ω := by
      rw [hd]
      exact_mod_cast (Nat.not_lt_of_ge hdn)
    have hsumCase :
        (∑ i ∈ Finset.range (n + 1),
          (if X (j + 2) ω = (i : ℝ) then
            (i : ℝ) * f (j + 2) +
              revenue f (fun q => (p q : ℝ)) (fun q => X q ω) (j + 1)
                (s - i)
           else 0)) =
          (d : ℝ) * f (j + 2) +
            revenue f (fun q => (p q : ℝ)) (fun q => X q ω) (j + 1)
              (s - d) := by
      rw [hsumEq]
      simp [hdn]
    have hrev :
        revenue f (fun q => (p q : ℝ)) (fun q => X q ω) (j + 2) s =
          (d : ℝ) * f (j + 2) +
            revenue f (fun q => (p q : ℝ)) (fun q => X q ω) (j + 1)
              (s - d) := by
      simp [revenue, not_lt_of_ge hseat, hmiddleD, hd]
    rw [hsumCase]
    simpa [htail] using hrev
  · have hdn' : n + 1 ≤ d := by omega
    have hdR : (n : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hdn'
    have hseat : (p (j + 1) : ℝ) ≤ s := by linarith
    have hdGt : n < d := by omega
    have htail : (n : ℝ) < X (j + 2) ω := by
      rw [hd]
      exact_mod_cast hdGt
    have hsumCase :
        (∑ i ∈ Finset.range (n + 1),
          (if X (j + 2) ω = (i : ℝ) then
            (i : ℝ) * f (j + 2) +
              revenue f (fun q => (p q : ℝ)) (fun q => X q ω) (j + 1)
                (s - i)
           else 0)) = 0 := by
      rw [hsumEq]
      simp [hdn]
    by_cases hmiddle : s < (p (j + 1) : ℝ) + (d : ℝ)
    · have hrev :
          revenue f (fun q => (p q : ℝ)) (fun q => X q ω) (j + 2) s =
            (s - (p (j + 1) : ℝ)) * f (j + 2) +
              revenue f (fun q => (p q : ℝ)) (fun q => X q ω) (j + 1)
                (p (j + 1) : ℝ) := by
        simp [revenue, not_lt_of_ge hseat, hmiddle, hd]
      rw [hsumCase]
      simpa [htail] using hrev
    · have hqeq : s - (p (j + 1) : ℝ) = (d : ℝ) := by
        have hqge : (d : ℝ) ≤ s - (p (j + 1) : ℝ) := by linarith
        linarith [hreshi, hdR]
      have hsdeq : s - (d : ℝ) = (p (j + 1) : ℝ) := by linarith
      have hrev :
          revenue f (fun q => (p q : ℝ)) (fun q => X q ω) (j + 2) s =
            (s - (p (j + 1) : ℝ)) * f (j + 2) +
              revenue f (fun q => (p q : ℝ)) (fun q => X q ω) (j + 1)
                (p (j + 1) : ℝ) := by
        simp [revenue, not_lt_of_ge hseat, hmiddle, hqeq, hsdeq, hd]
      rw [hsumCase]
      simpa [htail] using hrev

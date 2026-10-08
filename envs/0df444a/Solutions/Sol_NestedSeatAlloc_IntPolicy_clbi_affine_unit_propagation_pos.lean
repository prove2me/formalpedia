-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.clbi_affine_unit_propagation_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:38:19.139796+00:00
-- url     : https://prove2.me/submissions/ef4f5514-679c-4127-9511-ce45d5a0d8ea

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_next_demand_atom_tail_expectation
import Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_weighted_atom_tail_affine

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) (k : ℕ) (hk : 0 < k) (p : ℕ → ℕ)
    (hunit : ∀ m : ℕ, ∃ a b : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        expRevenue P X f (fun j => (p j : ℝ)) k s = a + b * s) :
    ∀ m : ℕ, ∃ a b : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        expRevenue P X f (fun j => (p j : ℝ)) (k + 1) s = a + b * s := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk) with ⟨j, rfl⟩
  intro m
  by_cases hm : m < p (j + 1)
  · obtain ⟨A, B, hAB⟩ := hunit m
    have hmR : (m : ℝ) + 1 ≤ (p (j + 1) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hm
    refine ⟨A, B, ?_⟩
    intro s hs
    have hrec :
        expRevenue P X f (fun i => (p i : ℝ)) ((j + 1) + 1) s =
          expRevenue P X f (fun i => (p i : ℝ)) (j + 1) s := by
      rw [expRevenue, expRevenue]
      apply integral_congr_ae
      filter_upwards [] with ω
      have hseat : s ≤ (p (j + 1) : ℝ) := le_trans hs.2 hmR
      by_cases hlt : s < (p (j + 1) : ℝ)
      · simp [revenue, hlt]
      · have hsEq : s = (p (j + 1) : ℝ) :=
          le_antisymm hseat (le_of_not_gt hlt)
        subst s
        by_cases hpos : 0 < X (j + 2) ω
        · have hmid : (p (j + 1) : ℝ) <
              (p (j + 1) : ℝ) + X (j + 2) ω := by linarith
          simp [revenue, hmid]
        · have hxzero : X (j + 2) ω = 0 :=
            le_antisymm (le_of_not_gt hpos) (hM.nonneg (j + 2) ω)
          simp [revenue, hxzero]
    rw [hrec]
    exact hAB s hs
  · have hpk : p (j + 1) ≤ m := Nat.le_of_not_gt hm
    let n : ℕ := m - p (j + 1)
    have hmn : m = p (j + 1) + n := by
      dsimp [n]
      omega
    have hmnR : (m : ℝ) = (p (j + 1) : ℝ) + (n : ℝ) := by
      exact_mod_cast hmn
    let a : ℝ := (p (j + 1) : ℝ)
    let c : ℝ := f (j + 2)
    let g : ℝ → ℝ := expRevenue P X f (fun i => (p i : ℝ)) (j + 1)
    let H : ℝ → ℝ := expRevenue P X f (fun i => (p i : ℝ)) (j + 2)
    let w : ℕ → ℝ := fun i => P.real {ω | X (j + 2) ω = (i : ℝ)}
    let tailWeight : ℝ := P.real {ω | (n : ℝ) < X (j + 2) ω}
    have hshift : ∀ i : ℕ, i ≤ n →
        ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
          ((m - i : ℕ) : ℝ) ≤ s - i ∧
            s - i ≤ ((m - i : ℕ) : ℝ) + 1 := by
      intro i hi s hs
      have him : i ≤ m := by omega
      have hmi : ((m - i : ℕ) : ℝ) + (i : ℝ) = (m : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel him
      constructor
      · linarith [hs.1, hmi]
      · linarith [hs.2, hmi]
    have hshiftedUnit : ∀ i : ℕ, i ≤ n →
        ∃ ai bi : ℝ, ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
          g (s - i) = ai + bi * (s - i) := by
      intro i hi
      obtain ⟨ai, bi, hbi⟩ := hunit (m - i)
      refine ⟨ai, bi, ?_⟩
      intro s hs
      have htranslated : s - i ∈
          Set.Icc ((m - i : ℕ) : ℝ) (((m - i : ℕ) : ℝ) + 1) :=
        ⟨(hshift i hi s hs).1, (hshift i hi s hs).2⟩
      exact hbi (s - i) htranslated
    have hexpect : ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        H s = (∑ i ∈ Finset.range (n + 1),
          w i * ((i : ℝ) * c + g (s - i))) +
          tailWeight * ((s - a) * c + g a) := by
      intro s hs
      have hs' : s ∈ Set.Icc
          ((p (j + 1) : ℝ) + (n : ℝ))
          ((p (j + 1) : ℝ) + (n : ℝ) + 1) := by
        rw [← hmnR]
        exact hs
      have hbridge := clbi_next_demand_atom_tail_expectation
        P X f hM hint (j + 1) n (by omega) p s hs'
      simpa [H, w, tailWeight, c, a, g] using hbridge
    obtain ⟨A, B, hAB⟩ := clbi_weighted_atom_tail_affine
      n m c a tailWeight (g a) w g H hshiftedUnit hexpect
    exact ⟨A, B, hAB⟩

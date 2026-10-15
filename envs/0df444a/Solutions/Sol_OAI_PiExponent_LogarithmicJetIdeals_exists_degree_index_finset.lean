-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.exists_degree_index_finset
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:39:57.065455+00:00
-- url     : https://prove2.me/submissions/8bf533bb-68ad-444a-ba28-c899100a984b

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

theorem solution {n : Nat} (m : Nat) :
    ∃ S : Finset (Fin n → Nat),
      ∀ d : Fin n → Nat, d ∈ S ↔ (∑ k, d k) = m := by
  classical
  let S : Finset (Fin n → Nat) :=
    (Fintype.piFinset (fun _ : Fin n => Finset.range (m + 1))).filter
      (fun d => (∑ k, d k) = m)
  refine ⟨S, ?_⟩
  intro d
  dsimp [S]
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨_, hsum⟩
    exact hsum
  · intro hsum
    refine ⟨?_, hsum⟩
    intro k
    apply Nat.lt_succ_of_le
    calc
      d k ≤ ∑ i : Fin n, d i :=
        Finset.single_le_sum (fun i hi => Nat.zero_le _) (Finset.mem_univ k)
      _ = m := hsum
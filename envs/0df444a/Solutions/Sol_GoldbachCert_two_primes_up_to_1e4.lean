-- Prove2me | solution 1 for GoldbachCert.two_primes_up_to_1e4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T16:02:18.635253+00:00
-- url     : https://prove2.me/submissions/5793cf6f-5d16-4d0e-aec1-2c488daec136

import Mathlib
import Definitions.Def_GoldbachCertWitness

set_option maxRecDepth 100000

namespace GoldbachCert

/-- Trial division up to the square root, as a computable test. -/
def isPrimeB (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range (Nat.sqrt n + 1)).all (fun d => decide (d < 2) || decide (n % d ≠ 0))

theorem isPrimeB_sound : ∀ {n : Nat}, isPrimeB n = true → Nat.Prime n := by
  intro n h
  simp only [isPrimeB, Bool.and_eq_true] at h
  obtain ⟨h2, hall⟩ := h
  have h2' : 2 ≤ n := of_decide_eq_true h2
  rw [List.all_eq_true] at hall
  refine Nat.prime_def_le_sqrt.2 ⟨h2', ?_⟩
  intro d hd2 hds hdvd
  have hmem : d ∈ List.range (Nat.sqrt n + 1) := by
    simp only [List.mem_range]; omega
  have hd := hall d hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq, ne_eq] at hd
  rcases hd with h | h
  · omega
  · exact h (Nat.dvd_iff_mod_eq_zero.mp hdvd)

def okAt (i p : Nat) : Bool := isPrimeB p && isPrimeB (2 * i + 4 - p)

def checkedFrom : Nat → List Nat → Bool
  | _, [] => true
  | i, p :: ps => okAt i p && checkedFrom (i + 1) ps

theorem checkedFrom_spec : ∀ (l : List Nat) (i : Nat), checkedFrom i l = true →
    ∀ (j : Nat), j < l.length →
      Nat.Prime (l.getD j 0) ∧ Nat.Prime (2 * (i + j) + 4 - l.getD j 0)
  | [], i, _, j, hj => absurd hj (by simp)
  | p :: ps, i, h, 0, _ => by
      simp only [checkedFrom, okAt, Bool.and_eq_true] at h
      exact ⟨isPrimeB_sound h.1.1, isPrimeB_sound h.1.2⟩
  | p :: ps, i, h, j + 1, hj => by
      simp only [checkedFrom, okAt, Bool.and_eq_true] at h
      have ih := checkedFrom_spec ps (i + 1) h.2 j (by simpa using hj)
      have e1 : (p :: ps).getD (j + 1) 0 = ps.getD j 0 := by simp
      rw [e1]
      refine ⟨ih.1, ?_⟩
      have e2 : 2 * (i + (j + 1)) + 4 = 2 * (i + 1 + j) + 4 := by omega
      rw [e2]; exact ih.2

theorem cert : checkedFrom 0 witness = true := by decide +kernel

theorem witness_length : witness.length = 4999 := rfl

end GoldbachCert

theorem solution (n : Nat) (h4 : 4 ≤ n) (heven : Even n) (hN : n ≤ 10000) :
    ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨k, hk⟩ := heven
  set i := (n - 4) / 2 with hi
  have hik : n = 2 * i + 4 := by omega
  have hlen : i < GoldbachCert.witness.length := by
    rw [GoldbachCert.witness_length]; omega
  obtain ⟨hp, hq⟩ := GoldbachCert.checkedFrom_spec GoldbachCert.witness 0 GoldbachCert.cert i hlen
  have hq' : Nat.Prime (n - GoldbachCert.witness.getD i 0) := by
    have e : 2 * (0 + i) + 4 = n := by omega
    rwa [e] at hq
  refine ⟨GoldbachCert.witness.getD i 0, n - GoldbachCert.witness.getD i 0, hp, hq', ?_⟩
  have h2 := hq'.two_le
  omega

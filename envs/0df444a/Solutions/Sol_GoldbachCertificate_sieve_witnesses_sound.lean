-- Prove2me | solution 1 for GoldbachCertificate.sieve_witnesses_sound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T00:33:43.845323+00:00
-- url     : https://prove2.me/submissions/7b0102c8-00e1-438a-8cd6-27b101959433

import Definitions.Def_GoldbachCertificate
import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false

namespace GoldbachCertificate

private lemma primeCheck_spec (p : ℕ) : primeCheck p = true ↔ Nat.Prime p := by
  simp only [primeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun m hm hms => ?_⟩
    exact (h m (by omega)).resolve_left (by omega)
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun m hm => ?_⟩
    by_cases hm2 : m < 2
    · exact Or.inl hm2
    · exact Or.inr (h m (by omega) (by omega))

private lemma PrimeTree.contains_prime (tree : PrimeTree) (n : ℕ)
    (hc : tree.check = true) (hn : tree.contains n = true) : Nat.Prime n := by
  induction tree with
  | empty => simp [PrimeTree.contains] at hn
  | node p left right ihl ihr =>
    simp only [PrimeTree.check, Bool.and_eq_true] at hc
    simp only [PrimeTree.contains] at hn
    split_ifs at hn with heq hlt
    · subst n
      exact (primeCheck_spec p).mp hc.1.1
    · exact ihl hc.1.2 hn
    · exact ihr hc.2 hn

private lemma rows_sound (rows : List (ℕ × ℕ)) (tree : PrimeTree)
    (ht : tree.check = true) :
    ∀ first smallBound : ℕ, checkRows first smallBound tree rows = true →
      ∀ n : ℕ, 2 * first ≤ n → n < 2 * (first + rows.length) → Even n →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ smallBound ∧ n = p + q := by
  induction rows with
  | nil =>
    intro first smallBound h n hlo hhi he
    simp only [List.length_nil, Nat.add_zero] at hhi
    omega
  | cons row rows ih =>
    rcases row with ⟨p, q⟩
    intro first smallBound h n hlo hhi he
    simp only [checkRows, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hn : n = 2 * first
    · exact ⟨p, q, tree.contains_prime p ht h.1.1.1.1,
        tree.contains_prime q ht h.1.1.1.2, h.1.1.2, hn.trans h.1.2.symm⟩
    · rcases he with ⟨k, hk⟩
      have hlo' : 2 * (first + 1) ≤ n := by omega
      have hhi' : n < 2 * (first + 1 + rows.length) := by
        simp only [List.length_cons] at hhi
        omega
      exact ih (first + 1) smallBound h.2 n hlo' hhi' ⟨k, hk⟩

end GoldbachCertificate

private lemma prime_mem_survivors (q lo hi cutoff : ℕ) (hq : q.Prime)
    (hlo : lo ≤ q) (hhi : q ≤ hi) : q ∈ GoldbachSieve.survivors lo hi cutoff := by
  unfold GoldbachSieve.survivors
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨max_le hq.two_le hlo, hhi⟩, ?_⟩
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro r hr
  rcases Finset.mem_filter.mp hr with ⟨hrmem, hrdvd, hrne⟩
  have hrprime : r.Prime := (Finset.mem_filter.mp hrmem).2
  exact hrne ((Nat.prime_dvd_prime_iff_eq hrprime hq).mp hrdvd)

theorem solution (first smallBound lo hi cutoff : ℕ) (tree : GoldbachCertificate.PrimeTree)
    (rows : List (ℕ × ℕ)) (ht : tree.check = true)
    (hr : GoldbachCertificate.checkRows first smallBound tree rows = true)
    (hcover : lo ≤ 2 * first - smallBound)
    (n : ℕ) (hlo : 2 * first ≤ n) (hhi : n < 2 * (first + rows.length))
    (hnhi : n ≤ hi) (he : Even n) :
    ∃ p ∈ ((Finset.Icc 2 smallBound).filter Nat.Prime),
      ∃ q ∈ GoldbachSieve.survivors lo hi cutoff, n = p + q := by
  rcases GoldbachCertificate.rows_sound rows tree ht first smallBound hr n hlo hhi he
    with ⟨p, q, hp, hq, hps, hsum⟩
  refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hps⟩, hp⟩,
    q, prime_mem_survivors q lo hi cutoff hq (by omega) (by omega), hsum⟩

#print axioms solution

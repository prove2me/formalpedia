-- Prove2me | solution 1 for NConjecture.n_conjecture_implies_abc
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T09:20:45.072054+00:00
-- url     : https://prove2.me/submissions/bf60eb26-663a-49dc-8d93-5e40564a2589

import Mathlib
import Definitions.Def_NConjecture_Defs
namespace NConjecture

theorem n_conjecture_implies_abc (h : conjAt 3) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → Nat.Coprime b c → Nat.Coprime a c →
        a + b = c →
        (c : ℝ) < K * (∏ p ∈ (a * b * c).primeFactors, (p : ℝ)) ^ (1 + ε) := by
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨2 * C, by linarith, ?_⟩
  intro a b c ha hb' hc hab hbc hac habc
  set t : Fin 3 → ℤ := ![(a : ℤ), b, -(c : ℤ)] with ht
  have habcZ : (a : ℤ) + b = c := by exact_mod_cast habc
  have hadm : admissible 3 t := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [ht, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      omega
    · apply Nat.dvd_one.mp
      have h1 : Finset.univ.gcd (fun i => (t i).natAbs) ∣ (t 0).natAbs :=
        Finset.gcd_dvd (Finset.mem_univ 0)
      have h2 : Finset.univ.gcd (fun i => (t i).natAbs) ∣ (t 1).natAbs :=
        Finset.gcd_dvd (Finset.mem_univ 1)
      have e0 : (t 0).natAbs = a := by simp [ht]
      have e1 : (t 1).natAbs = b := by simp [ht]
      rw [e0] at h1; rw [e1] at h2
      rw [← hab.gcd_eq_one]
      exact Nat.dvd_gcd h1 h2
    · intro s hs hne
      fin_cases s <;> simp [ht] at hs hne ⊢ <;>
        first | omega | (exfalso; exact hne (by decide)) | skip
  have key := hb t hadm
  have hcle : (c : ℝ) ≤ ((Finset.univ.sup fun i => (t i).natAbs : ℕ) : ℝ) := by
    have h3 : (t 2).natAbs ≤ Finset.univ.sup fun i => (t i).natAbs :=
      Finset.le_sup (f := fun i => (t i).natAbs) (Finset.mem_univ 2)
    have h2 : (t 2).natAbs = c := by simp [ht]
    rw [h2] at h3
    exact_mod_cast h3
  have hprod : (∏ i, (t i).natAbs) = a * b * c := by
    simp [ht, Fin.prod_univ_three]
  rw [hprod] at key
  have hexp : (2 * ((3 : ℕ) : ℝ) - 5 + ε) = 1 + ε := by push_cast; ring
  rw [hexp] at key
  have hrad : (Brocard.radical (a * b * c) : ℝ) = ∏ p ∈ (a * b * c).primeFactors, (p : ℝ) := by
    unfold Brocard.radical; push_cast; rfl
  rw [hrad] at key
  have hpos : 0 < (∏ p ∈ (a * b * c).primeFactors, (p : ℝ)) ^ (1 + ε) := by
    apply Real.rpow_pos_of_pos
    exact Finset.prod_pos (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
  nlinarith

end NConjecture

theorem solution (h : NConjecture.conjAt 3) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → Nat.Coprime b c → Nat.Coprime a c →
        a + b = c →
        (c : ℝ) < K * (∏ p ∈ (a * b * c).primeFactors, (p : ℝ)) ^ (1 + ε) :=
  NConjecture.n_conjecture_implies_abc h ε hε

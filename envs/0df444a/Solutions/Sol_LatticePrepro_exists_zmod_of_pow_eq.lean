-- Prove2me | solution 1 for LatticePrepro.exists_zmod_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:27:54.568761+00:00
-- url     : https://prove2.me/submissions/f07b9b8b-d4d6-4765-958d-cf123dbac5ae

import Mathlib


namespace LatticePrepro

open Polynomial

variable {Ω : Type*} [Field Ω]

/-- A fixed point of Frobenius in a field of characteristic `p` lies in the prime field. -/
private lemma exists_zmod_of_pow_eq {p : ℕ} [hp : Fact p.Prime] [Algebra (ZMod p) Ω] {c : Ω}
    (hc : c ^ p = c) : ∃ a : ZMod p, algebraMap (ZMod p) Ω a = c := by
  classical
  set q : Polynomial Ω := X ^ p - X with hq
  have hq0 : q ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero Ω hp.out.one_lt
  have hdeg : q.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq Ω hp.out.one_lt
  set S : Finset Ω := Finset.univ.image (algebraMap (ZMod p) Ω) with hS
  have hSsub : S ⊆ q.roots.toFinset := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot.def, hq, eval_sub, eval_pow, eval_X,
      ← map_pow, ZMod.pow_card, sub_self]
  have hcard : q.roots.toFinset.card ≤ S.card := by
    calc q.roots.toFinset.card ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
      _ ≤ q.natDegree := card_roots' q
      _ = p := hdeg
      _ = S.card := by
        rw [hS, Finset.card_image_of_injective _ (algebraMap (ZMod p) Ω).injective,
          Finset.card_univ, ZMod.card]
  have hSeq : S = q.roots.toFinset := Finset.eq_of_subset_of_card_le hSsub hcard
  have hcmem : c ∈ q.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot.def, hq, eval_sub, eval_pow, eval_X, hc,
      sub_self]
  rw [← hSeq] at hcmem
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hcmem
  exact ⟨a, ha⟩

end LatticePrepro

open Polynomial
variable {Ω : Type*} [Field Ω]
theorem solution {p : ℕ} [hp : Fact p.Prime] [Algebra (ZMod p) Ω] {c : Ω}
    (hc : c ^ p = c) : ∃ a : ZMod p, algebraMap (ZMod p) Ω a = c :=
  @LatticePrepro.exists_zmod_of_pow_eq Ω _ p _ _ c hc

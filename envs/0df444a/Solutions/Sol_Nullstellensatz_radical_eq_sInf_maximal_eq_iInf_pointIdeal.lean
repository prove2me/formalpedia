-- Prove2me | solution 1 for Nullstellensatz.radical_eq_sInf_maximal_eq_iInf_pointIdeal
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T22:41:38.546085+00:00
-- url     : https://prove2.me/submissions/8de58644-52e9-4a23-89ba-1c1b8dd33652

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace NSSAux

variable {K : Type*} [Field K] {n : ℕ}

lemma pow_zero_helper {x : K} {r : ℕ} (h : x ^ r = 0) : x = 0 := by
  by_contra hx
  exact (pow_ne_zero r hx) h

lemma mem_vanishingIdeal (U : Set (Fin n → K)) (p : MvPolynomial (Fin n) K) :
    p ∈ Nullstellensatz.vanishingIdeal U ↔ ∀ a ∈ U, eval a p = 0 := Iff.rfl

lemma mem_zeroSet (J : Ideal (MvPolynomial (Fin n) K)) (a : Fin n → K) :
    a ∈ Nullstellensatz.zeroSet J ↔ ∀ f ∈ J, eval a f = 0 := Iff.rfl

/-- Every polynomial is congruent to its value at `a` modulo the point ideal of `a`. -/
lemma sub_C_eval_mem (a : Fin n → K) (p : MvPolynomial (Fin n) K) :
    p - C (eval a p) ∈ Nullstellensatz.pointIdeal a := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    have e : p + q - C (eval a (p + q)) = (p - C (eval a p)) + (q - C (eval a q)) := by
      simp only [map_add]; ring
    rw [e]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    have e : p * X i - C (eval a (p * X i)) =
        (p - C (eval a p)) * X i + C (eval a p) * (X i - C (a i)) := by
      simp only [map_mul, eval_X]; ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    exact Ideal.subset_span ⟨i, rfl⟩

lemma pointIdeal_eq_ker (a : Fin n → K) :
    Nullstellensatz.pointIdeal a = RingHom.ker (eval a) := by
  apply le_antisymm
  · rw [Nullstellensatz.pointIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  · intro p hp
    rw [RingHom.mem_ker] at hp
    have h := sub_C_eval_mem a p
    rwa [hp, map_zero, sub_zero] at h

lemma mem_pointIdeal_iff (a : Fin n → K) (p : MvPolynomial (Fin n) K) :
    p ∈ Nullstellensatz.pointIdeal a ↔ eval a p = 0 := by
  rw [pointIdeal_eq_ker, RingHom.mem_ker]

lemma pointIdeal_isMaximal (a : Fin n → K) : (Nullstellensatz.pointIdeal a).IsMaximal := by
  rw [pointIdeal_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C _⟩)

lemma vanishingIdeal_singleton_eq (a : Fin n → K) :
    Nullstellensatz.vanishingIdeal {a} = Nullstellensatz.pointIdeal a := by
  ext p
  rw [mem_vanishingIdeal, mem_pointIdeal_iff]
  simp

lemma nullstellensatz' [IsAlgClosed K] (J : Ideal (MvPolynomial (Fin n) K)) :
    Nullstellensatz.vanishingIdeal (Nullstellensatz.zeroSet J) = J.radical := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) J]
  ext p
  simp only [MvPolynomial.mem_vanishingIdeal_iff, MvPolynomial.mem_zeroLocus_iff,
    MvPolynomial.coe_aeval_eq_eval]
  rfl

lemma isMaximal_iff' [IsAlgClosed K] (m : Ideal (MvPolynomial (Fin n) K)) :
    m.IsMaximal ↔ ∃ a : Fin n → K, m = Nullstellensatz.pointIdeal a := by
  rw [MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    ext p
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, mem_pointIdeal_iff]
    exact Iff.rfl
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    ext p
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, mem_pointIdeal_iff]
    exact Iff.rfl

end NSSAux

theorem solution {K : Type*} [Field K] [IsAlgClosed K]
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) K)) :
    J.radical = sInf {m | J ≤ m ∧ m.IsMaximal} ∧
      J.radical = ⨅ a ∈ Nullstellensatz.zeroSet J, Nullstellensatz.pointIdeal a := by
  constructor
  · have h1 : J.radical.jacobson = J.radical :=
      IsJacobsonRing.out inferInstance (Ideal.radical_isRadical J)
    rw [← h1, Ideal.jacobson]
    congr 1
    ext m
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hle, hm⟩
      exact ⟨le_trans Ideal.le_radical hle, hm⟩
    · rintro ⟨hle, hm⟩
      exact ⟨(hm.isPrime.radical_le_iff).mpr hle, hm⟩
  · rw [← NSSAux.nullstellensatz']
    ext p
    rw [NSSAux.mem_vanishingIdeal, Submodule.mem_iInf]
    constructor
    · intro h a
      rw [Submodule.mem_iInf]
      intro ha
      exact (NSSAux.mem_pointIdeal_iff a p).mpr (h a ha)
    · intro h a ha
      have h' := (Submodule.mem_iInf _).mp (h a) ha
      exact (NSSAux.mem_pointIdeal_iff a p).mp h'

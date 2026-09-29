-- Prove2me | solution 1 for Nullstellensatz.algebraicSet_radicalIdeal_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T22:41:42.345931+00:00
-- url     : https://prove2.me/submissions/13a5edd1-e52b-4c2e-9321-061799e0c0dd

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

theorem solution {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ} :
    Set.BijOn (Nullstellensatz.zeroSet (K := K) (n := n)) {J | J.IsRadical}
      {W | Nullstellensatz.IsAlgebraicSet W} ∧
    (∀ J₁ J₂ : Ideal (MvPolynomial (Fin n) K), J₁ ≤ J₂ →
      Nullstellensatz.zeroSet J₂ ⊆ Nullstellensatz.zeroSet J₁) ∧
    (∀ J : Ideal (MvPolynomial (Fin n) K), J.IsRadical →
      Nullstellensatz.vanishingIdeal (Nullstellensatz.zeroSet J) = J) ∧
    (∀ W : Set (Fin n → K), Nullstellensatz.IsAlgebraicSet W →
      Nullstellensatz.zeroSet (Nullstellensatz.vanishingIdeal W) = W) := by
  have hrad : ∀ J : Ideal (MvPolynomial (Fin n) K), J.IsRadical →
      Nullstellensatz.vanishingIdeal (Nullstellensatz.zeroSet J) = J := by
    intro J hJ
    rw [NSSAux.nullstellensatz', hJ.radical]
  have hzr : ∀ J : Ideal (MvPolynomial (Fin n) K),
      Nullstellensatz.zeroSet J.radical = Nullstellensatz.zeroSet J := by
    intro J
    ext a
    simp only [NSSAux.mem_zeroSet]
    constructor
    · intro h f hf
      exact h f (Ideal.le_radical hf)
    · intro h f hf
      obtain ⟨r, hr⟩ := hf
      have h' := h _ hr
      rw [map_pow] at h'
      exact NSSAux.pow_zero_helper h'
  refine ⟨⟨?_, ?_, ?_⟩, ?_, hrad, ?_⟩
  · intro J _
    exact ⟨J, rfl⟩
  · intro J₁ h₁ J₂ h₂ he
    rw [← hrad J₁ h₁, ← hrad J₂ h₂]
    exact congrArg Nullstellensatz.vanishingIdeal he
  · rintro W ⟨J, rfl⟩
    exact ⟨J.radical, Ideal.radical_isRadical J, hzr J⟩
  · intro J₁ J₂ h a ha
    rw [NSSAux.mem_zeroSet] at ha ⊢
    exact fun f hf => ha f (h hf)
  · rintro W ⟨J, rfl⟩
    apply Set.Subset.antisymm
    · intro a ha
      rw [NSSAux.mem_zeroSet] at ha ⊢
      intro f hf
      apply ha f
      rw [NSSAux.mem_vanishingIdeal]
      intro b hb
      rw [NSSAux.mem_zeroSet] at hb
      exact hb f hf
    · intro a ha
      rw [NSSAux.mem_zeroSet]
      intro f hf
      rw [NSSAux.mem_vanishingIdeal] at hf
      exact hf a ha

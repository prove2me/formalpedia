-- Prove2me | solution 1 for NgoFL.discriminant_eq_subDiscriminant_mul_resultant_sq
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T18:17:51.630905+00:00
-- url     : https://prove2.me/submissions/4ffbeda6-10be-4c2c-9fba-9488306135d6

import Mathlib
import Definitions.Def_NgoEndoscopicDiscriminant

open NgoFL

namespace NgoFLFactor

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- The root indexed by `negIdx P i` is the negative of the root indexed by `i`. -/
lemma root_negIdx (i : ι) : P.root (negIdx P i) = - P.root i := by
  simp [negIdx]

lemma root'_negIdx (i : ι) (y : N) : P.root' (negIdx P i) y = - P.root' i y := by
  have h : P.root (negIdx P i) = - P.root i := root_negIdx P i
  simp [RootPairing.root', h]

lemma negIdx_involutive : Function.Involutive (negIdx P) := by
  intro i
  apply P.root.injective
  rw [root_negIdx, root_negIdx, neg_neg]

variable [Fintype ι] [DecidableEq ι]

/-- A half system `L` of `sᶜ` and its negative partition `sᶜ`. -/
lemma compl_eq_union {s L : Finset ι} (hL : IsHalfSystem P sᶜ L) :
    sᶜ = L ∪ L.image (negIdx P) := by
  ext i
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · intro hi
    rcases hL.xor_mem i hi with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨negIdx P i, h, negIdx_involutive P i⟩
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact hL.subset h
    · exact hL.neg_mem a (hL.subset ha)

lemma disjoint_image_negIdx {s L : Finset ι} (hL : IsHalfSystem P sᶜ L) :
    Disjoint L (L.image (negIdx P)) := by
  rw [Finset.disjoint_right]
  rintro i hi hiL
  simp only [Finset.mem_image] at hi
  obtain ⟨a, ha, rfl⟩ := hi
  have hmem : negIdx P a ∈ sᶜ := hL.subset hiL
  have hxor := hL.xor_mem (negIdx P a) hmem
  rw [negIdx_involutive P a] at hxor
  rcases hxor with ⟨-, h⟩ | ⟨-, h⟩
  · exact h ha
  · exact h hiL

end NgoFLFactor

/-- **Ngô, 1.10.3**: with `Φ = Φ_H ⊔ Λ ⊔ (-Λ)`, the discriminant factors as
`D_G = (-1)^{|Λ|} D_H (R^G_H)^2`. -/
theorem solution {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Fintype ι] [DecidableEq ι]
    (P : RootPairing ι R M N) (s L : Finset ι) (hL : IsHalfSystem P sᶜ L) (x : N) :
    discriminant P x
      = (-1) ^ L.card * (subDiscriminant P s x * resultant P L x ^ 2) := by
  have hinj : Set.InjOn (negIdx P) L :=
    fun a _ b _ h => (NgoFLFactor.negIdx_involutive P).injective h
  have hneg : ∏ i ∈ L.image (negIdx P), P.root' i x
      = (-1) ^ L.card * ∏ i ∈ L, P.root' i x := by
    rw [Finset.prod_image hinj]
    calc ∏ i ∈ L, P.root' (negIdx P i) x
        = ∏ i ∈ L, (-1 : R) * P.root' i x := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [NgoFLFactor.root'_negIdx]
          ring
      _ = (-1) ^ L.card * ∏ i ∈ L, P.root' i x := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hcompl : ∏ i ∈ sᶜ, P.root' i x
      = (-1) ^ L.card * (∏ i ∈ L, P.root' i x) ^ 2 := by
    rw [NgoFLFactor.compl_eq_union P hL,
      Finset.prod_union (NgoFLFactor.disjoint_image_negIdx P hL), hneg]
    ring
  calc discriminant P x
      = (∏ i ∈ s, P.root' i x) * ∏ i ∈ sᶜ, P.root' i x :=
        (Finset.prod_mul_prod_compl s fun i => P.root' i x).symm
    _ = (-1) ^ L.card * (subDiscriminant P s x * resultant P L x ^ 2) := by
        rw [hcompl]
        simp only [subDiscriminant, resultant]
        ring

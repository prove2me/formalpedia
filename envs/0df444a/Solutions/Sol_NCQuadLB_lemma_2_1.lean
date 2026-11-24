-- Prove2me | solution 1 for NCQuadLB.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-23T23:23:17.778196+00:00
-- url     : https://prove2.me/submissions/c0241657-4085-4278-b7e2-4e19784ea979

import Mathlib
import Definitions.Def_NCQuadLB_mindeg

open NCQuadLB

theorem solution {F : Type*} [Field F] {V : Type*} (f g : FreeAlgebra F V) (hf : f ≠ 0)
    (hg : g ≠ 0) : mindeg (f * g) = mindeg f + mindeg g := by
  classical
  set E := (FreeAlgebra.equivMonoidAlgebraFreeMonoid : FreeAlgebra F V ≃ₐ[F] MonoidAlgebra F (FreeMonoid V)) with hE
  have hc : ∀ h : FreeAlgebra F V, NCFactorClosure607.Circuits.coeffs h = (E h).coeff := fun _ => rfl
  -- a word in the support has length at least mindeg
  have hle : ∀ (h : FreeAlgebra F V) (w : FreeMonoid V), (E h).coeff w ≠ 0 → mindeg h ≤ w.length := by
    intro h w hw
    unfold mindeg
    apply Nat.sInf_le
    refine ⟨w, ?_, rfl⟩
    rw [hc]
    simpa using hw
  -- a nonzero element has a word of length exactly mindeg
  have hex : ∀ h : FreeAlgebra F V, h ≠ 0 → ∃ w, (E h).coeff w ≠ 0 ∧ w.length = mindeg h := by
    intro h hh
    have hne : (E h).coeff ≠ 0 := by
      rw [Ne, MonoidAlgebra.coeff_eq_zero]
      exact fun h0 => hh (E.injective (by rw [h0, map_zero]))
    obtain ⟨w0, hw0⟩ := Finsupp.ne_iff.mp hne
    have hS : ((fun w : FreeMonoid V => w.length) '' ↑(NCFactorClosure607.Circuits.coeffs h).support).Nonempty :=
      ⟨w0.length, w0, by rw [hc]; simpa using hw0, rfl⟩
    obtain ⟨w, hw, hwl⟩ := Nat.sInf_mem hS
    refine ⟨w, ?_, hwl⟩
    rw [hc] at hw
    simpa using hw
  obtain ⟨u, hu, hul⟩ := hex f hf
  obtain ⟨v, hv, hvl⟩ := hex g hg
  have hmul : E (f * g) = E f * E g := map_mul E f g
  -- lower bound: every word of f*g has length ≥ mindeg f + mindeg g
  have hlow : ∀ w, (E (f * g)).coeff w ≠ 0 → mindeg f + mindeg g ≤ w.length := by
    intro w hw
    by_contra hlt
    push_neg at hlt
    apply hw
    rw [hmul, MonoidAlgebra.coeff_mul, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro m1 hm1
    rw [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro m2 hm2
    rw [if_neg]
    intro heq
    have h1 := hle f m1 (Finsupp.mem_support_iff.mp hm1)
    have h2 := hle g m2 (Finsupp.mem_support_iff.mp hm2)
    have := FreeMonoid.length_mul m1 m2
    rw [heq] at this
    omega
  -- the coefficient of u*v is the product of the coefficients
  have hcoef : (E (f * g)).coeff (u * v) = (E f).coeff u * (E g).coeff v := by
    rw [hmul, MonoidAlgebra.coeff_mul, Finsupp.sum]
    rw [Finset.sum_eq_single u]
    · rw [Finsupp.sum, Finset.sum_eq_single v]
      · simp
      · intro m2 _ hne
        rw [if_neg]
        intro heq
        apply hne
        have := congrArg FreeMonoid.toList heq
        simp only [FreeMonoid.toList_mul] at this
        exact FreeMonoid.toList.injective (List.append_cancel_left this)
      · intro hn
        rw [Finsupp.mem_support_iff, not_not] at hn
        simp [hn]
    · intro m1 hm1 hne
      rw [Finsupp.sum]
      apply Finset.sum_eq_zero
      intro m2 hm2
      rw [if_neg]
      intro heq
      apply hne
      have h1 := hle f m1 (Finsupp.mem_support_iff.mp hm1)
      have h2 := hle g m2 (Finsupp.mem_support_iff.mp hm2)
      have hl := FreeMonoid.length_mul m1 m2
      have hl2 := FreeMonoid.length_mul u v
      rw [heq] at hl
      have hlen : m1.length = u.length := by omega
      have := congrArg FreeMonoid.toList heq
      simp only [FreeMonoid.toList_mul] at this
      exact FreeMonoid.toList.injective (List.append_inj this hlen).1
    · intro hn
      rw [Finsupp.mem_support_iff, not_not] at hn
      simp [hn]
  have huv : (E (f * g)).coeff (u * v) ≠ 0 := by
    rw [hcoef]; exact mul_ne_zero hu hv
  apply le_antisymm
  · have := hle (f * g) (u * v) huv
    rw [FreeMonoid.length_mul, hul, hvl] at this
    exact this
  · obtain ⟨w, hw, hwl⟩ := hex (f * g) (mul_ne_zero hf hg)
    rw [← hwl]
    exact hlow w hw

-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.mvPolynomial_exists_coordinate_transcendence_basis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:33:46.29649+00:00
-- url     : https://prove2.me/submissions/c61eb32e-4f0c-4a3d-bce4-391fa13161cc

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open Algebra in
theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    ∃ s : Finset (Fin (m + 1)),
      AlgebraicIndependent Complex
        (fun i : s => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
          (FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P))
          (MvPolynomial.X i.1)) ∧
      s.card =
        (Algebra.trdeg Complex
          (FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P))).toNat := by
  classical
  set B := MvPolynomial (Fin (m + 1)) Complex ⧸ P
  set K := FractionRing B
  set f : Fin (m + 1) → K := fun i =>
    algebraMap (MvPolynomial (Fin (m + 1)) Complex) K (MvPolynomial.X i) with hf
  let φ : MvPolynomial (Fin (m + 1)) Complex →ₐ[Complex] K :=
    (IsScalarTower.toAlgHom Complex B K).comp (Ideal.Quotient.mkₐ Complex P)
  have hφ : ∀ p, φ p = algebraMap (MvPolynomial (Fin (m + 1)) Complex) K p := fun p => rfl
  have hadj : adjoin Complex (Set.range f) = φ.range := by
    have : Set.range f = φ '' Set.range MvPolynomial.X := by
      ext y; simp [hf, hφ]
    rw [this, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
  have hmem : ∀ b : B, algebraMap B K b ∈ adjoin Complex (Set.range f) := by
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [hadj]; exact ⟨p, rfl⟩
  haveI : Algebra.IsAlgebraic (adjoin Complex (Set.range f)) K := by
    constructor
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    set α : adjoin Complex (Set.range f) := ⟨_, hmem a⟩
    set β : adjoin Complex (Set.range f) := ⟨_, hmem b⟩
    have hβ : β ≠ 0 := by
      intro h
      have : algebraMap B K b = 0 := congrArg Subtype.val h
      exact nonZeroDivisors.ne_zero hb
        ((IsFractionRing.injective B K).eq_iff.mp (this.trans (map_zero _).symm))
    refine ⟨Polynomial.C β * Polynomial.X - Polynomial.C α, ?_, ?_⟩
    · intro h
      have := congrArg (fun p => Polynomial.coeff p 1) h
      simp at this
      exact hβ this
    · have hb0 : algebraMap B K b ≠ 0 := by
        intro h; exact hβ (Subtype.ext h)
      simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change algebraMap B K b * (algebraMap B K a / algebraMap B K b) - algebraMap B K a = 0
      rw [mul_div_cancel₀ _ hb0, sub_self]
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := Complex) (Set.range f)
  have htfin : t.Finite := (Set.finite_range f).subset hts
  let g : K → Fin (m + 1) := fun y => if h : y ∈ Set.range f then h.choose else 0
  have hg : ∀ y ∈ t, f (g y) = y := by
    intro y hy
    have h : y ∈ Set.range f := hts hy
    simp only [g, dif_pos h]; exact h.choose_spec
  let s : Finset (Fin (m + 1)) := htfin.toFinset.image g
  have hginj : Set.InjOn g t := fun y hy y' hy' h => by
    rw [← hg y hy, ← hg y' hy', h]
  have hsmem : ∀ i : s, f i.1 ∈ t := by
    rintro ⟨i, hi⟩
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hi
    rw [Set.Finite.mem_toFinset] at hy
    simpa [hg y hy] using hy
  let ψ : s → t := fun i => ⟨f i.1, hsmem i⟩
  have hψ : Function.Injective ψ := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hj
    rw [Set.Finite.mem_toFinset] at hy hy'
    have : f (g y) = f (g y') := congrArg Subtype.val h
    rw [hg y hy, hg y' hy'] at this
    simp [this]
  refine ⟨s, ?_, ?_⟩
  · exact ht.1.comp ψ hψ
  · have hc := ht.cardinalMk_eq_trdeg
    rw [← hc, Finset.card_image_of_injOn (by simpa using hginj)]
    have : Fintype t := htfin.fintype
    simp [Set.Finite.card_toFinset, Cardinal.mk_fintype]

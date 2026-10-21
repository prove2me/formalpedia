-- Prove2me | solution 1 for LPCA.localization_nontrivial_iff
-- status  : ACCEPTED   (prove)
-- author  : @kaiyue
-- created : 2026-10-20T22:46:10.523095+00:00
-- url     : https://prove2.me/submissions/c650a56f-cc5c-4eb4-ae6b-2dcc01f20d7f

import Definitions.Def_LPCA
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false

open LPCA

universe u

theorem solution
    {V : Type u} [DecidableEq V] [Fintype V]
    (k : Type u) [Field k] (K : Complex V) (F : Finset V) :
    Nontrivial (LocalizedFaceRing k K F) ↔ F ∈ K.faces := by
  classical
  constructor
  · intro hnontrivial
    letI := hnontrivial
    by_contra hF
    have hz : invertedMonomial k K F = 0 := by
      unfold invertedMonomial variableClass
      rw [← map_prod]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.subset_span ⟨F, hF, rfl⟩
    have hu := IsLocalization.Away.algebraMap_isUnit
      (S := LocalizedFaceRing k K F) (invertedMonomial k K F)
    have hmap : algebraMap (FaceRing k K) (LocalizedFaceRing k K F)
        (invertedMonomial k K F) = 0 := by
      simpa only [map_zero] using congrArg
        (algebraMap (FaceRing k K) (LocalizedFaceRing k K F)) hz
    rw [hmap] at hu
    exact not_isUnit_zero hu
  · intro hF
    let evaluation : MvPolynomial V k →+* k :=
      MvPolynomial.eval (fun j => if j ∈ F then 1 else 0)
    have hkernel : srIdeal k K ≤ RingHom.ker evaluation := by
      apply Ideal.span_le.mpr
      rintro p ⟨G, hG, rfl⟩
      change evaluation (∏ j ∈ G, MvPolynomial.X j) = 0
      have hnsub : ¬ G ⊆ F := fun hGF => hG (K.down_closed hF hGF)
      obtain ⟨j, hjG, hjF⟩ := Finset.not_subset.mp hnsub
      rw [map_prod]
      apply Finset.prod_eq_zero hjG
      simp [evaluation, hjF]
    let quotientEvaluation : FaceRing k K →+* k :=
      Ideal.Quotient.lift (srIdeal k K) evaluation
        (fun p hp => RingHom.mem_ker.mp (hkernel hp))
    have heval : quotientEvaluation (invertedMonomial k K F) = 1 := by
      unfold invertedMonomial
      rw [map_prod]
      apply Finset.prod_eq_one
      intro j hj
      change evaluation (MvPolynomial.X j) = 1
      simp [evaluation, hj]
    have hunit : IsUnit (quotientEvaluation (invertedMonomial k K F)) := by
      rw [heval]
      exact isUnit_one
    let localizedEvaluation : LocalizedFaceRing k K F →+* k :=
      IsLocalization.Away.lift (invertedMonomial k K F) hunit
    exact localizedEvaluation.domain_nontrivial

#print axioms solution

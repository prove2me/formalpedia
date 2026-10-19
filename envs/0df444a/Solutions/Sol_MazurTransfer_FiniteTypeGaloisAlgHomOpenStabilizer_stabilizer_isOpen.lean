-- Prove2me | solution 1 for MazurTransfer.FiniteTypeGaloisAlgHomOpenStabilizer.stabilizer_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T23:15:21.883502+00:00
-- url     : https://prove2.me/submissions/34521089-c18e-4433-932b-9b98f8d2b4f4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a field-valued point of a finite type algebra has an
open Galois stabilizer for the Krull topology of an algebraic extension.
Named downstream consumer: geometric points on the finite actual norm
fibres and continuous Kummer cocycles.
-/
import Mathlib
noncomputable section
theorem solution (F K A : Type) [Field F] [Field K] [Algebra F K]
    [Algebra.IsIntegral F K] [CommRing A] [Algebra F A] [Algebra.FiniteType F A] (f : A →ₐ[F] K) :
    IsOpen {σ : K ≃ₐ[F] K | σ.toAlgHom.comp f = f} := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra F A).FG)
  have hset : {σ : K ≃ₐ[F] K | σ.toAlgHom.comp f = f} =
      ⋂ a ∈ s, {σ : K ≃ₐ[F] K | σ (f a) = f a} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h a ha
      exact AlgHom.congr_fun h a
    · intro h
      apply AlgHom.ext_of_adjoin_eq_top hs
      exact fun a ha => h a ha
  rw [hset]
  apply isOpen_biInter_finset
  intro a ha
  exact stabilizer_isOpen_of_isIntegral (f a)

#print axioms solution

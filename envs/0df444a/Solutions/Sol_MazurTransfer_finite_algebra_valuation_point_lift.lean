-- Prove2me | solution 1 for MazurTransfer.finite_algebra_valuation_point_lift
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T10:20:27.993978+00:00
-- url     : https://prove2.me/submissions/e1e0a717-9941-4bef-9964-fd4f4acabcc2

/- Copyright (c) 2026 Vas and contributors. Apache-2.0. Design boundary: standalone finite-algebra valuation point extension. Named downstream consumer: integral coordinates of the actual selected chi13 norm-cocycle points. -/
import Mathlib
noncomputable section
universe u v w

theorem solution
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Module.Finite R A] {F : Type w} [Field F] [Algebra R F]
    (P : ValuationSubring F) [Algebra R P] [IsScalarTower R P F]
    (f : A →ₐ[R] F) :
    ∃ fP : A →ₐ[R] P, ∀ a, (fP a : F) = f a := by
  have hf : ∀ a : A, f a ∈ P := by
    intro a
    apply (Subring.isIntegrallyClosed_iff (S := P)).mp inferInstance
    exact ((Algebra.IsIntegral.isIntegral (R := R) a).map f).tower_top
  refine ⟨{ (f.toRingHom.codRestrict P hf) with commutes' := ?_ }, ?_⟩
  · intro r
    apply Subtype.ext
    change f (algebraMap R A r) = algebraMap P F (algebraMap R P r)
    rw [f.commutes]
    exact IsScalarTower.algebraMap_apply R P F r
  · intro a
    rfl

#print axioms solution

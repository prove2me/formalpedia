-- Prove2me | solution 1 for LieAlgebraBasis.map_lie_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-28T01:51:20.011649+00:00
-- url     : https://prove2.me/submissions/7c48fe77-2c2d-4ee8-9827-8504c686f238

import Mathlib

attribute [local instance 100] LieRing.ofAssociativeRing

theorem solution {R L M ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] (B : Module.Basis ι R L)
    (f : L →ₗ[R] Module.End R M)
    (h : ∀ i j, ⁅f (B i), f (B j)⁆ = f ⁅B i, B j⁆) :
    ∀ x y : L, ⁅f x, f y⁆ = f ⁅x, y⁆ := by
  set F1 : L →ₗ[R] L →ₗ[R] Module.End R M :=
    LinearMap.mk₂ R (fun x y => ⁅f x, f y⁆)
      (fun x₁ x₂ y => by
        show ⁅f (x₁ + x₂), f y⁆ = ⁅f x₁, f y⁆ + ⁅f x₂, f y⁆
        rw [map_add, add_lie])
      (fun a x y => by
        show ⁅f (a • x), f y⁆ = a • ⁅f x, f y⁆
        rw [map_smul, smul_lie])
      (fun x y₁ y₂ => by
        show ⁅f x, f (y₁ + y₂)⁆ = ⁅f x, f y₁⁆ + ⁅f x, f y₂⁆
        rw [map_add, lie_add])
      (fun a x y => by
        show ⁅f x, f (a • y)⁆ = a • ⁅f x, f y⁆
        rw [map_smul, lie_smul]) with hF1
  set F2 : L →ₗ[R] L →ₗ[R] Module.End R M :=
    LinearMap.mk₂ R (fun x y => f ⁅x, y⁆)
      (fun x₁ x₂ y => by
        show f ⁅x₁ + x₂, y⁆ = f ⁅x₁, y⁆ + f ⁅x₂, y⁆
        rw [add_lie, map_add])
      (fun a x y => by
        show f ⁅a • x, y⁆ = a • f ⁅x, y⁆
        rw [smul_lie, map_smul])
      (fun x y₁ y₂ => by
        show f ⁅x, y₁ + y₂⁆ = f ⁅x, y₁⁆ + f ⁅x, y₂⁆
        rw [lie_add, map_add])
      (fun a x y => by
        show f ⁅x, a • y⁆ = a • f ⁅x, y⁆
        rw [lie_smul, map_smul]) with hF2
  have hEq : F1 = F2 := by
    refine LinearMap.ext_basis B B (fun i j => ?_)
    show ⁅f (B i), f (B j)⁆ = f ⁅B i, B j⁆
    exact h i j
  intro x y
  have hxy := congrArg (fun G : L →ₗ[R] L →ₗ[R] Module.End R M => G x y) hEq
  exact hxy

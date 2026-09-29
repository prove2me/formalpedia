-- Prove2me | solution 1 for Module.FaithfullyFlat.exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7431e743-8833-5747-8307-92ce3ba3524f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_FaithfullyFlat_exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    (R W k : Type) [CommRing R] [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W]
    [Field k] [IsAlgClosed k] [Algebra R k] :
    ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (_ : Algebra R k') (_ : Algebra W k') (_ : Algebra k k'),
      IsScalarTower R W k' ∧ IsScalarTower R k k' := by
  classical
  haveI : Nontrivial (k ⊗[R] W) := inferInstance
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (k ⊗[R] W)
  haveI := h𝔪
  letI : Field ((k ⊗[R] W) ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  obtain ⟨π⟩ : Nonempty (k ⊗[R] W →+* AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) :=
    ⟨(algebraMap ((k ⊗[R] W) ⧸ 𝔪) (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪))).comp (Ideal.Quotient.mk 𝔪)⟩
  refine ⟨AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪), inferInstance, inferInstance,
    (π.comp (algebraMap R (k ⊗[R] W))).toAlgebra,
    (π.comp (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := W)).toRingHom).toAlgebra,
    (π.comp (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := k) (B := W))).toAlgebra, ?_, ?_⟩
  · letI : Algebra R (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) := (π.comp (algebraMap R (k ⊗[R] W))).toAlgebra
    letI : Algebra W (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) :=
      (π.comp (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := W)).toRingHom).toAlgebra
    exact IsScalarTower.of_algebraMap_eq (fun r => by
      show π (algebraMap R (k ⊗[R] W) r) = π (Algebra.TensorProduct.includeRight (algebraMap R W r))
      rw [AlgHom.commutes])
  · letI : Algebra R (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) := (π.comp (algebraMap R (k ⊗[R] W))).toAlgebra
    letI : Algebra k (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) :=
      (π.comp (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := k) (B := W))).toAlgebra
    exact IsScalarTower.of_algebraMap_eq (fun r => by
      show π (algebraMap R (k ⊗[R] W) r) = π (Algebra.TensorProduct.includeLeftRingHom (algebraMap R k r))
      rfl)

end S_Module_FaithfullyFlat_exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed
end P2MW
export P2MW.S_Module_FaithfullyFlat_exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed (solution)

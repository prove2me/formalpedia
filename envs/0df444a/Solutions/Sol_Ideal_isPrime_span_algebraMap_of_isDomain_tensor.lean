-- Prove2me | solution 1 for Ideal.isPrime_span_algebraMap_of_isDomain_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e2d80cb5-9dd5-5ffd-a285-7cae497af704

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_isPrime_span_algebraMap_of_isDomain_tensor

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] {κ : Type*} [Field κ] [Algebra R κ]
    (ϖ : R) (hker : RingHom.ker (algebraMap R κ) = Ideal.span {ϖ}) (hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal)
    [IsDomain (κ ⊗[R] A)] : (Ideal.span {algebraMap R A ϖ} : Ideal A).IsPrime := by
  classical
  set I : Ideal R := Ideal.span {ϖ} with hI
  haveI : I.IsMaximal := hmax
  letI : Field (R ⧸ I) := Ideal.Quotient.field I

  let qk : R ⧸ I →+* κ := Ideal.Quotient.lift I (algebraMap R κ) (fun r hr => by
    rwa [← RingHom.mem_ker, hker])
  letI : Algebra (R ⧸ I) κ := qk.toAlgebra
  haveI : IsScalarTower R (R ⧸ I) κ :=
    IsScalarTower.of_algebraMap_eq (fun r => (Ideal.Quotient.lift_mk I _ _).symm)

  let g : A →ₐ[R] κ ⊗[R] A := Algebra.TensorProduct.includeRight
  have hP : (RingHom.ker g).IsPrime := RingHom.ker_isPrime _
  suffices h : RingHom.ker g = Ideal.span {algebraMap R A ϖ} by rwa [← h]
  apply le_antisymm
  · intro a ha
    rw [RingHom.mem_ker] at ha
    change (1 : κ) ⊗ₜ[R] a = 0 at ha

    let e1 : (A ⧸ I.map (algebraMap R A)) ≃ₐ[A] A ⊗[R] (R ⧸ I) :=
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I
    let e2 : A ⊗[R] (R ⧸ I) ≃ₐ[R] (R ⧸ I) ⊗[R] A := Algebra.TensorProduct.comm R A (R ⧸ I)
    let j : (R ⧸ I) ⊗[R] A →ₐ[R ⧸ I] κ ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] A) := Algebra.TensorProduct.includeRight
    haveI : Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] A) := Module.Free.of_divisionRing _ _
    have hj : Function.Injective j := Algebra.TensorProduct.includeRight_injective qk.injective
    let e3 : κ ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] A) ≃ₗ[κ] κ ⊗[R] A :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) κ κ A

    have hcomp : ∀ b : A, e3 (j (e2 (e1 (Ideal.Quotient.mk _ b)))) = (1 : κ) ⊗ₜ[R] b := by
      intro b
      have h1 : e1 (Ideal.Quotient.mk _ b) = b ⊗ₜ[R] (1 : R ⧸ I) :=
        Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk A I b
      rw [h1]
      change e3 ((1 : κ) ⊗ₜ[R ⧸ I] (Algebra.TensorProduct.comm R A (R ⧸ I) (b ⊗ₜ[R] (1 : R ⧸ I)))) = _
      rw [Algebra.TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    have h0 : e3 (j (e2 (e1 (Ideal.Quotient.mk _ a)))) = 0 := by rw [hcomp, ha]
    rw [LinearEquiv.map_eq_zero_iff, ← map_zero j, hj.eq_iff, EmbeddingLike.map_eq_zero_iff,
      EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.map_span, Set.image_singleton] at h0
    exact h0
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    change (1 : κ) ⊗ₜ[R] (algebraMap R A ϖ) = 0
    have hϖ0 : algebraMap R κ ϖ = 0 := by
      rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self ϖ
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, hϖ0,
      TensorProduct.zero_tmul]

end S_Ideal_isPrime_span_algebraMap_of_isDomain_tensor
end P2MW
export P2MW.S_Ideal_isPrime_span_algebraMap_of_isDomain_tensor (solution)

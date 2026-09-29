-- Prove2me | solution 1 for HopfAlgebra.mem_hopfKer_iff_one_tmul_mem_hopfKer_baseChange_fractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2ab535b1-7f66-5115-9d87-34764ab86801

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_mem_hopfKer_iff_one_tmul_mem_hopfKer_baseChange_fractionRing

set_option autoImplicit false

open scoped TensorProduct

universe u v w

set_option maxHeartbeats 1600000

namespace HopfAlgebra
p2m_export "HopfAlgebra" "coaction coaction_apply hopfKer mem_hopfKer_iff"
p2m_open "HopfAlgebra"

section REDcore

variable {R : Type u} [CommRing R] (T : Type u) [CommRing T] [Algebra R T]
variable {A : Type v} [CommRing A] [HopfAlgebra R A] {B : Type w} [CommRing B] [HopfAlgebra R B]
variable (π : A →ₐc[R] B)

noncomputable def redEps : (T ⊗[R] A) ⊗[T] (T ⊗[R] B) ≃ₐ[T] T ⊗[R] (A ⊗[R] B) :=
  (Algebra.TensorProduct.cancelBaseChange R T T (T ⊗[R] A) B).trans (Algebra.TensorProduct.assoc R R T T A B)

theorem redEps_tmul (t₁ t₂ : T) (a : A) (b : B) :
    redEps T ((t₁ ⊗ₜ[R] a) ⊗ₜ[T] (t₂ ⊗ₜ[R] b)) = (t₂ * t₁) ⊗ₜ[R] (a ⊗ₜ[R] b) := by
  rw [redEps, AlgEquiv.trans_apply, Algebra.TensorProduct.cancelBaseChange_tmul, TensorProduct.smul_tmul',
    smul_eq_mul, Algebra.TensorProduct.assoc_tmul]

theorem bc_tmul (t : T) (a : A) :
    ((Bialgebra.TensorProduct.map (BialgHom.id T T) π : T ⊗[R] A →ₐc[T] T ⊗[R] B) : T ⊗[R] A →ₐ[T] T ⊗[R] B)
      (t ⊗ₜ[R] a) = t ⊗ₜ[R] π a := by
  show (Bialgebra.TensorProduct.map (BialgHom.id T T) π) (t ⊗ₜ[R] a) = t ⊗ₜ[R] π a
  rw [Bialgebra.TensorProduct.map_tmul]
  rfl

theorem redEps_map_tttc (t : T) (c : A ⊗[R] A) :
    redEps T (Algebra.TensorProduct.map (AlgHom.id T (T ⊗[R] A))
        ((Bialgebra.TensorProduct.map (BialgHom.id T T) π : T ⊗[R] A →ₐc[T] T ⊗[R] B) :
          T ⊗[R] A →ₐ[T] T ⊗[R] B)
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R T R T T T A A
        (((1 : T) ⊗ₜ[T] t) ⊗ₜ[R] c)))
    = t ⊗ₜ[R] (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B) c) := by
  induction c using TensorProduct.induction_on with
  | zero =>
      rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero, map_zero, map_zero, TensorProduct.tmul_zero]
  | tmul a₁ a₂ =>
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, bc_tmul, redEps_tmul, mul_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rfl
  | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, hx, hy]

theorem redEps_coaction_one_tmul (x : A) :
    redEps T (coaction (Bialgebra.TensorProduct.map (BialgHom.id T T) π : T ⊗[R] A →ₐc[T] T ⊗[R] B)
      ((1 : T) ⊗ₜ[R] x)) = (1 : T) ⊗ₜ[R] coaction π x := by
  rw [coaction_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply, redEps_map_tttc, coaction_apply]

theorem redEps_one_tmul_tmul_one (x : A) :
    redEps T ((((1 : T) ⊗ₜ[R] x) : T ⊗[R] A) ⊗ₜ[T] (1 : T ⊗[R] B)) = (1 : T) ⊗ₜ[R] (x ⊗ₜ[R] (1 : B)) := by
  rw [Algebra.TensorProduct.one_def, redEps_tmul, mul_one]

theorem mem_hopfKer_iff_one_tmul_mem_hopfKer_baseChange'
    (hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : A ⊗[R] B →ₐ[R] T ⊗[R] (A ⊗[R] B)))
    (x : A) :
    x ∈ hopfKer π ↔
      (1 : T) ⊗ₜ[R] x ∈ hopfKer
        (Bialgebra.TensorProduct.map (BialgHom.id T T) π : T ⊗[R] A →ₐc[T] T ⊗[R] B) := by
  rw [mem_hopfKer_iff, mem_hopfKer_iff, ← (redEps (R := R) T (A := A) (B := B)).injective.eq_iff,
    redEps_coaction_one_tmul, redEps_one_tmul_tmul_one]
  constructor
  · intro h
    rw [h]
  · intro h
    exact hinj h

end REDcore

end HopfAlgebra

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (x : H) :
    x ∈ HopfAlgebra.hopfKer qc ↔
      (1 : K) ⊗ₜ[R] x ∈ HopfAlgebra.hopfKer
        (Bialgebra.TensorProduct.map (BialgHom.id K K) qc : K ⊗[R] H →ₐc[K] K ⊗[R] H') :=
  HopfAlgebra.mem_hopfKer_iff_one_tmul_mem_hopfKer_baseChange' K qc
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K)) x

end S_HopfAlgebra_mem_hopfKer_iff_one_tmul_mem_hopfKer_baseChange_fractionRing
end P2MW
export P2MW.S_HopfAlgebra_mem_hopfKer_iff_one_tmul_mem_hopfKer_baseChange_fractionRing (solution)

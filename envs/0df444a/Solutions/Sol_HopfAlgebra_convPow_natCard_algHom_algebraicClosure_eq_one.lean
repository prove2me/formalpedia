-- Prove2me | solution 1 for HopfAlgebra.convPow_natCard_algHom_algebraicClosure_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ac615b5c-cf97-5725-bcee-0e68fe45c110

import Mathlib
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_convPow_natCard_algHom_algebraicClosure_eq_one

set_option autoImplicit false
open scoped TensorProduct
universe v

namespace S17KillQ

section Units

variable {R K T : Type*} [CommRing R] [CommRing K] [HopfAlgebra R K] [CommRing T] [Algebra R T]

def antipodeAlgHom : K →ₐ[R] K :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])

theorem antipodeAlgHom_apply (k : K) : antipodeAlgHom (R := R) k = HopfAlgebra.antipode R k :=
  rfl

theorem lift_comp_comp (ψ : K →ₐ[R] T) (X Y : K →ₐ[R] K) :
    Algebra.TensorProduct.lift (ψ.comp X) (ψ.comp Y) (fun _ _ => Commute.all _ _)
      = ψ.comp (Algebra.TensorProduct.lift X Y (fun _ _ => Commute.all _ _)) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext; intro a; simp
  · apply AlgHom.ext; intro b; simp

theorem toConv_mul_toConv_comp_antipode (ψ : K →ₐ[R] T) :
    WithConv.toConv ψ * WithConv.toConv (ψ.comp (antipodeAlgHom (R := R))) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro c
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  have hlift := lift_comp_comp ψ (AlgHom.id R K) (antipodeAlgHom (R := R))
  rw [AlgHom.comp_id] at hlift
  have hlin : (Algebra.TensorProduct.lift (AlgHom.id R K) (antipodeAlgHom (R := R))
        (fun _ _ => Commute.all _ _)).toLinearMap
      = LinearMap.mul' R K ∘ₗ (HopfAlgebra.antipode R).lTensor K := by
    apply TensorProduct.ext'
    intro a b
    rfl
  have hx := LinearMap.congr_fun hlin (Coalgebra.comul c)
  rw [AlgHom.toLinearMap_apply, LinearMap.comp_apply,
    HopfAlgebra.mul_antipode_lTensor_comul_apply] at hx
  show Algebra.TensorProduct.lift (WithConv.ofConv (WithConv.toConv ψ))
      (WithConv.ofConv (WithConv.toConv (ψ.comp (antipodeAlgHom (R := R)))))
      (fun _ _ => Commute.all _ _) (Coalgebra.comul c) = _
  rw [WithConv.ofConv_toConv, WithConv.ofConv_toConv, hlift, AlgHom.comp_apply, hx,
    AlgHom.commutes]

theorem toConv_comp_antipode_mul_toConv (ψ : K →ₐ[R] T) :
    WithConv.toConv (ψ.comp (antipodeAlgHom (R := R))) * WithConv.toConv ψ = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro c
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  have hlift := lift_comp_comp ψ (antipodeAlgHom (R := R)) (AlgHom.id R K)
  rw [AlgHom.comp_id] at hlift
  have hlin : (Algebra.TensorProduct.lift (antipodeAlgHom (R := R)) (AlgHom.id R K)
        (fun _ _ => Commute.all _ _)).toLinearMap
      = LinearMap.mul' R K ∘ₗ (HopfAlgebra.antipode R).rTensor K := by
    apply TensorProduct.ext'
    intro a b
    rfl
  have hx := LinearMap.congr_fun hlin (Coalgebra.comul c)
  rw [AlgHom.toLinearMap_apply, LinearMap.comp_apply,
    HopfAlgebra.mul_antipode_rTensor_comul_apply] at hx
  show Algebra.TensorProduct.lift (WithConv.ofConv (WithConv.toConv (ψ.comp (antipodeAlgHom (R := R)))))
      (WithConv.ofConv (WithConv.toConv ψ))
      (fun _ _ => Commute.all _ _) (Coalgebra.comul c) = _
  rw [WithConv.ofConv_toConv, WithConv.ofConv_toConv, hlift, AlgHom.comp_apply, hx,
    AlgHom.commutes]

theorem isUnit_toConv (ψ : K →ₐ[R] T) : IsUnit (WithConv.toConv ψ) :=
  ⟨⟨WithConv.toConv ψ, WithConv.toConv (ψ.comp (antipodeAlgHom (R := R))),
    toConv_mul_toConv_comp_antipode ψ, toConv_comp_antipode_mul_toConv ψ⟩, rfl⟩

end Units

theorem convPow_natCard_eq_one_point {R K L : Type*} [CommRing R] [CommRing K] [HopfAlgebra R K]
    [CommRing L] [Algebra R L] (ψ : WithConv (K →ₐ[R] L)) : ψ ^ Nat.card (K →ₐ[R] L) = 1 := by
  letI : Group (WithConv (K →ₐ[R] L)) :=
    groupOfIsUnit (fun x => by rw [← WithConv.toConv_ofConv x]; exact isUnit_toConv (R := R) (WithConv.ofConv x))
  have h := pow_card_eq_one' (G := WithConv (K →ₐ[R] L)) (x := ψ)
  rw [Nat.card_congr (WithConv.equiv (K →ₐ[R] L))] at h
  exact h

theorem exists_algHom_forall_mem_iff {L B : Type*} [Field L] [IsAlgClosed L] [CommRing B] [Algebra L B]
    [Algebra.FiniteType L B] (𝔪 : Ideal B) [𝔪.IsMaximal] :
    ∃ Ψ : B →ₐ[L] L, ∀ x, Ψ x = 0 ↔ x ∈ 𝔪 := by
  letI : Field (B ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType L B)
  have hsurj : Function.Surjective ((Ideal.Quotient.mkₐ L 𝔪).comp f) :=
    (Ideal.Quotient.mkₐ_surjective L 𝔪).comp hf
  have halg : Algebra.IsAlgebraic L (B ⧸ 𝔪) := by
    rw [Algebra.isAlgebraic_iff_isIntegral, ← algebraMap_isIntegral_iff]
    have h := MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
      (((Ideal.Quotient.mkₐ L 𝔪).comp f : MvPolynomial (Fin n) L →ₐ[L] B ⧸ 𝔪) : MvPolynomial (Fin n) L →+* B ⧸ 𝔪)
      hsurj
    have e : (((Ideal.Quotient.mkₐ L 𝔪).comp f : MvPolynomial (Fin n) L →ₐ[L] B ⧸ 𝔪) :
        MvPolynomial (Fin n) L →+* B ⧸ 𝔪).comp MvPolynomial.C = algebraMap L (B ⧸ 𝔪) := by
      ext x
      simp
    rwa [e] at h
  refine ⟨(IsAlgClosed.lift : B ⧸ 𝔪 →ₐ[L] L).comp (Ideal.Quotient.mkₐ L 𝔪), fun x => ?_⟩
  rw [AlgHom.comp_apply, map_eq_zero_iff (IsAlgClosed.lift : B ⧸ 𝔪 →ₐ[L] L)
      (IsAlgClosed.lift : B ⧸ 𝔪 →ₐ[L] L).toRingHom.injective,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]

theorem eq_zero_of_forall_algHom_eq_zero {L B : Type*} [Field L] [IsAlgClosed L] [CommRing B] [Algebra L B]
    [Algebra.FiniteType L B] [IsReduced B] (x : B) (hx : ∀ Ψ : B →ₐ[L] L, Ψ x = 0) : x = 0 := by
  haveI : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := L)

  have hmax : ∀ m : Ideal B, m.IsMaximal → x ∈ m := by
    intro m hm
    obtain ⟨Ψ, hΨ⟩ := exists_algHom_forall_mem_iff (L := L) m
    exact (hΨ x).1 (hx Ψ)

  have hjac : x ∈ (⊥ : Ideal B).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro J ⟨-, hJ⟩
    exact hmax J hJ
  rw [← Ideal.radical_eq_jacobson] at hjac
  obtain ⟨n, hn⟩ := hjac
  exact IsReduced.eq_zero x ⟨n, by simpa using hn⟩

theorem eq_of_forall_algHom_apply_eq {R K : Type*} [CommRing R] [CommRing K] [HopfAlgebra R K]
    [Algebra.FiniteType R K] [Module.Flat R K] (L : Type*) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    (hRL : Function.Injective (algebraMap R L)) (a b : K) (h : ∀ ψ : K →ₐ[R] L, ψ a = ψ b) : a = b := by
  have hinj := Algebra.TensorProduct.includeRight_injective (R := R) (A := L) (B := K) hRL
  apply hinj
  rw [← sub_eq_zero, ← map_sub]
  haveI : Algebra.FiniteType L (L ⊗[R] K) := Algebra.FiniteType.baseChange L
  haveI : IsReduced (L ⊗[R] K) := HopfAlgebra.isReduced_of_finiteType_of_charZero L (L ⊗[R] K)
  apply eq_zero_of_forall_algHom_eq_zero (L := L)
  intro Ψ
  have h1 := h ((Ψ.restrictScalars R).comp (Algebra.TensorProduct.includeRight : K →ₐ[R] L ⊗[R] K))
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h1
  rw [map_sub, map_sub, h1, sub_self]

theorem comp_convPow {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Bialgebra R C]
    [Algebra R A] [Algebra R B] (h : A →ₐ[R] B) (f : WithConv (C →ₐ[R] A)) (n : ℕ) :
    h.comp (f ^ n).ofConv = (WithConv.toConv (h.comp f.ofConv) ^ n).ofConv := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, AlgHom.convOne_def (R := R) (A := A) (C := C),
        AlgHom.convOne_def (R := R) (A := B) (C := C), WithConv.ofConv_toConv, WithConv.ofConv_toConv,
        ← AlgHom.comp_assoc]
      congr 1
      apply AlgHom.ext
      intro r
      simp [Algebra.ofId_apply]
  | succ n ih =>
      rw [pow_succ, pow_succ, AlgHom.comp_convMul_distrib, ih, WithConv.toConv_ofConv]

theorem convPow_natCard_algHom_eq_one {R K : Type*} [CommRing R] [CommRing K] [HopfAlgebra R K]
    [Algebra.FiniteType R K] [Module.Flat R K] (L : Type*) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    (hRL : Function.Injective (algebraMap R L))
    (T : Type*) [CommRing T] [Algebra R T] (f : WithConv (K →ₐ[R] T)) :
    f ^ Nat.card (K →ₐ[R] L) = 1 := by
  set N := Nat.card (K →ₐ[R] L) with hN

  have hid : (WithConv.toConv (AlgHom.id R K)) ^ N = 1 := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro k
    apply eq_of_forall_algHom_apply_eq (R := R) L hRL
    intro ψ
    have h1 : ψ.comp ((WithConv.toConv (AlgHom.id R K)) ^ N).ofConv = ψ.comp (1 : WithConv (K →ₐ[R] K)).ofConv := by
      rw [comp_convPow, WithConv.ofConv_toConv, AlgHom.comp_id, convPow_natCard_eq_one_point]
      have h0 := comp_convPow ψ (WithConv.toConv (AlgHom.id R K)) 0
      rw [pow_zero, pow_zero] at h0
      exact h0.symm
    exact DFunLike.congr_fun h1 k

  have h2 := comp_convPow f.ofConv (WithConv.toConv (AlgHom.id R K)) N
  rw [hid, WithConv.ofConv_toConv, AlgHom.comp_id, WithConv.toConv_ofConv] at h2

  apply WithConv.ofConv_injective
  rw [← h2]
  have h3 := comp_convPow f.ofConv (WithConv.toConv (AlgHom.id R K)) 0
  rw [pow_zero, pow_zero] at h3
  exact h3

end S17KillQ

theorem S17KillQ.flat_of_flat' {M : Type*} [AddCommGroup M] {m₁ m₂ : Module ℤ M}
    (h : @Module.Flat ℤ M _ _ m₁) : @Module.Flat ℤ M _ _ m₂ := by
  obtain rfl : m₁ = m₂ := Subsingleton.elim _ _
  exact h

open S17KillQ in
theorem solution
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (T : Type v) [CommRing T] (f : WithConv (K →ₐ[ℤ] T)) :
    f ^ Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 1 := by
  haveI : @Module.Flat ℤ K _ _ Algebra.toModule := flat_of_flat' inferInstance
  exact convPow_natCard_algHom_eq_one (R := ℤ) (AlgebraicClosure ℚ) (RingHom.injective_int _) T f

end S_HopfAlgebra_convPow_natCard_algHom_algebraicClosure_eq_one
end P2MW
export P2MW.S_HopfAlgebra_convPow_natCard_algHom_algebraicClosure_eq_one (solution)

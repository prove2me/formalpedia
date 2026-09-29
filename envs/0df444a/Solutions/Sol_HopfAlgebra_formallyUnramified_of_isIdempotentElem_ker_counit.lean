-- Prove2me | solution 1 for HopfAlgebra.formallyUnramified_of_isIdempotentElem_ker_counit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/90f320da-a716-5aa9-afb7-33ec2c900d1b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_formallyUnramified_of_isIdempotentElem_ker_counit

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

universe u v

namespace S42UNR

open HopfAlgebra

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]

noncomputable def antipodeAlgHom : A →ₐ[R] A :=
  AlgHom.ofLinearMap (antipode R) antipode_one fun a b => by rw [antipode_mul, mul_comm]

theorem lift_antipodeAlgHom_comp_apply {B : Type*} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (z : TensorProduct R A A) :
    Algebra.TensorProduct.lift (φ.comp antipodeAlgHom) φ (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R A ((antipode R).rTensor A z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul, antipodeAlgHom]
  | add x y hx hy => simp [map_add, hx, hy]

theorem lift_comp_antipodeAlgHom_apply {B : Type*} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (z : TensorProduct R A A) :
    Algebra.TensorProduct.lift φ (φ.comp antipodeAlgHom) (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R A ((antipode R).lTensor A z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul, antipodeAlgHom]
  | add x y hx hy => simp [map_add, hx, hy]

theorem comp_antipode_convMul {B : Type*} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    WithConv.toConv (φ.comp antipodeAlgHom) * WithConv.toConv φ = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (WithConv.toConv (φ.comp antipodeAlgHom) * WithConv.toConv φ) x = (1 : WithConv (A →ₐ[R] B)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
    lift_antipodeAlgHom_comp_apply, mul_antipode_rTensor_comul_apply, AlgHom.commutes]

theorem convMul_comp_antipode {B : Type*} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    WithConv.toConv φ * WithConv.toConv (φ.comp antipodeAlgHom) = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (WithConv.toConv φ * WithConv.toConv (φ.comp antipodeAlgHom)) x = (1 : WithConv (A →ₐ[R] B)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
    lift_comp_antipodeAlgHom_apply, mul_antipode_lTensor_comul_apply, AlgHom.commutes]

theorem convMul_apply_repr {B : Type*} [CommRing B] [Algebra R B] (φ ψ : A →ₐ[R] B) {a : A} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr R a ι𝓡) :
    (WithConv.toConv φ * WithConv.toConv ψ).ofConv a = ∑ i ∈ 𝓡.index, φ (𝓡.left i) * ψ (𝓡.right i) := by
  have h : ((WithConv.toConv φ * WithConv.toConv ψ).ofConv : A →ₐ[R] B).toLinearMap =
      (WithConv.toConv φ.toLinearMap * WithConv.toConv ψ.toLinearMap).ofConv :=
    congrArg WithConv.ofConv (AlgHom.toLinearMap_convMul (WithConv.toConv φ) (WithConv.toConv ψ))
  have h2 := LinearMap.congr_fun h a
  rw [AlgHom.toLinearMap_apply] at h2
  rw [h2]
  exact Coalgebra.Repr.convMul_apply 𝓡 _ _

end S42UNR

open S42UNR in
theorem solution
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    (hI : IsIdempotentElem (RingHom.ker (Bialgebra.counitAlgHom R A))) :
    Algebra.FormallyUnramified R A := by
  classical
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ N hN f g hfg

  have hfg' : ∀ a, f a - g a ∈ N := by
    intro a
    have := AlgHom.congr_fun hfg a
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 this
  have hN2 : ∀ x ∈ N, ∀ y ∈ N, x * y = 0 := by
    intro x hx y hy
    have : x * y ∈ N ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hy
    rwa [hN, Ideal.mem_bot] at this

  let finv : A →ₐ[R] B := f.comp antipodeAlgHom
  let h : A →ₐ[R] B := (WithConv.toConv finv * WithConv.toConv g).ofConv
  have hε : ∀ a, (WithConv.toConv finv * WithConv.toConv f).ofConv a = algebraMap R B (Coalgebra.counit a) := by
    intro a
    rw [comp_antipode_convMul]
    rfl
  let δ : A → B := fun a => h a - algebraMap R B (Coalgebra.counit a)
  have hδN : ∀ a, δ a ∈ N := by
    intro a
    let 𝓡 := Coalgebra.Repr.arbitrary R a
    show h a - algebraMap R B (Coalgebra.counit a) ∈ N
    rw [← hε a]
    show (WithConv.toConv finv * WithConv.toConv g).ofConv a - (WithConv.toConv finv * WithConv.toConv f).ofConv a ∈ N
    rw [convMul_apply_repr finv g 𝓡, convMul_apply_repr finv f 𝓡, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [← mul_sub]
    exact Ideal.mul_mem_left _ _ (by rw [← neg_sub]; exact N.neg_mem (hfg' _))

  have hδmul : ∀ a b, δ (a * b) = algebraMap R B (Coalgebra.counit b) * δ a + algebraMap R B (Coalgebra.counit a) * δ b := by
    intro a b
    have e1 : δ (a * b) = δ a * algebraMap R B (Coalgebra.counit b) + algebraMap R B (Coalgebra.counit a) * δ b + δ a * δ b := by
      show h (a * b) - algebraMap R B (Coalgebra.counit (a * b)) = _
      rw [map_mul, Bialgebra.counit_mul, map_mul]
      ring
    rw [e1, hN2 _ (hδN a) _ (hδN b), add_zero, mul_comm]

  have hδI : ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom R A), δ a = 0 := by
    intro a ha
    rw [← hI.eq] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      rw [hδmul, show Coalgebra.counit (R := R) x = 0 from hx, show Coalgebra.counit (R := R) y = 0 from hy, map_zero, zero_mul,
        zero_mul, add_zero]
    · intro x y hx hy
      show h (x + y) - algebraMap R B (Coalgebra.counit (x + y)) = 0
      have hx' : h x - algebraMap R B (Coalgebra.counit x) = 0 := hx
      have hy' : h y - algebraMap R B (Coalgebra.counit y) = 0 := hy
      rw [map_add, map_add, map_add]
      linear_combination hx' + hy'

  have hδ0 : ∀ a, δ a = 0 := by
    intro a
    have ha : a - algebraMap R A (Coalgebra.counit a) ∈ RingHom.ker (Bialgebra.counitAlgHom R A) := by
      rw [RingHom.mem_ker]
      show Coalgebra.counit (a - algebraMap R A (Coalgebra.counit a)) = 0
      rw [map_sub, Bialgebra.counit_algebraMap, sub_self]
    have h1 := hδI _ ha
    have h2 : δ (algebraMap R A (Coalgebra.counit a)) = 0 := by
      show h (algebraMap R A (Coalgebra.counit a)) - algebraMap R B (Coalgebra.counit (algebraMap R A (Coalgebra.counit (R := R) a))) = 0
      rw [AlgHom.commutes, Bialgebra.counit_algebraMap, sub_self]
    have h3 : δ a = δ (a - algebraMap R A (Coalgebra.counit a)) + δ (algebraMap R A (Coalgebra.counit a)) := by
      show h a - algebraMap R B (Coalgebra.counit a) =
        (h (a - algebraMap R A (Coalgebra.counit a)) - algebraMap R B (Coalgebra.counit (a - algebraMap R A (Coalgebra.counit a)))) +
        (h (algebraMap R A (Coalgebra.counit a)) - algebraMap R B (Coalgebra.counit (algebraMap R A (Coalgebra.counit (R := R) a))))
      rw [map_sub, map_sub (Coalgebra.counit (R := R) (A := A)), map_sub]
      ring
    rw [h3, h1, h2, add_zero]

  have hh : WithConv.toConv finv * WithConv.toConv g = 1 := by
    refine WithConv.ext (AlgHom.ext fun a => ?_)
    have := hδ0 a
    change h a - algebraMap R B (Coalgebra.counit a) = 0 at this
    rw [sub_eq_zero] at this
    exact this
  have h1 : WithConv.toConv f * WithConv.toConv finv = 1 := convMul_comp_antipode f
  have : WithConv.toConv g = WithConv.toConv f := by
    calc WithConv.toConv g = (WithConv.toConv f * WithConv.toConv finv) * WithConv.toConv g := by rw [h1, one_mul]
      _ = WithConv.toConv f * (WithConv.toConv finv * WithConv.toConv g) := mul_assoc _ _ _
      _ = WithConv.toConv f := by rw [hh, mul_one]
  exact (WithConv.toConv_injective this).symm

end S_HopfAlgebra_formallyUnramified_of_isIdempotentElem_ker_counit
end P2MW
export P2MW.S_HopfAlgebra_formallyUnramified_of_isIdempotentElem_ker_counit (solution)

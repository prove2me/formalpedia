-- Prove2me | solution 1 for HopfAlgebra.bijective_lift_coinvariants_and_bijective_mkQ_of_isHopfModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/cb6e10af-b673-5a92-ae5c-11d06225a840

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_bijective_lift_coinvariants_and_bijective_mkQ_of_isHopfModule

set_option autoImplicit false

open scoped TensorProduct

namespace H1

open Coalgebra HopfAlgebra WithConv

section ComulAntipode

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [HopfAlgebra R A]

theorem comul_comp_antipode :
    (comul : A →ₗ[R] A ⊗[R] A) ∘ₗ antipode R =
      TensorProduct.map (antipode R) (antipode R) ∘ₗ (TensorProduct.comm R A A).toLinearMap ∘ₗ
        (comul : A →ₗ[R] A ⊗[R] A) := by
  classical
  refine toConv_injective
    (left_inv_eq_right_inv
      (b := toConv ((comul : A →ₗ[R] A ⊗[R] A) ∘ₗ antipode R))
      (a := toConv (comul : A →ₗ[R] A ⊗[R] A))
      (c := toConv (TensorProduct.map (antipode R) (antipode R) ∘ₗ
        (TensorProduct.comm R A A).toLinearMap ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)))
      ?_ ?_)
  ·
    refine WithConv.ext (LinearMap.ext fun x => ?_)
    rw [(ℛ R x).convMul_apply, LinearMap.convOne_apply]
    show ∑ i ∈ (ℛ R x).index, comul (antipode R ((ℛ R x).left i)) * comul ((ℛ R x).right i) =
      algebraMap R (A ⊗[R] A) (counit x)
    calc ∑ i ∈ (ℛ R x).index, comul (antipode R ((ℛ R x).left i)) * comul ((ℛ R x).right i)
        = Bialgebra.comulAlgHom R A
            (∑ i ∈ (ℛ R x).index, antipode R ((ℛ R x).left i) * (ℛ R x).right i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul]
          rfl
      _ = algebraMap R (A ⊗[R] A) (counit x) := by
          rw [sum_antipode_mul_eq_algebraMap_counit, AlgHom.commutes]
  ·
    refine WithConv.ext (LinearMap.ext fun x => ?_)
    rw [(ℛ R x).convMul_apply, LinearMap.convOne_apply]

    let T : A →ₗ[R] A ⊗[R] A := TensorProduct.map (antipode R) (antipode R) ∘ₗ
      (TensorProduct.comm R A A).toLinearMap ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    let Φ : A ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A :=
      LinearMap.mul' R (A ⊗[R] A) ∘ₗ TensorProduct.map LinearMap.id T ∘ₗ
        (TensorProduct.assoc R A A A).symm.toLinearMap
    have hΦ : ∀ a b c : A, Φ (a ⊗ₜ (b ⊗ₜ c)) = (a ⊗ₜ b) * T c := by
      intro a b c
      simp [Φ]
    let Ψ : A → (A ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A) := fun l =>
      (TensorProduct.comm R A A).toLinearMap ∘ₗ
        TensorProduct.map (LinearMap.mul' R A ∘ₗ TensorProduct.map LinearMap.id (antipode R))
          (LinearMap.mulLeft R l ∘ₗ antipode R) ∘ₗ
        (TensorProduct.assoc R A A A).symm.toLinearMap
    have hΨ : ∀ l b c c' : A, Ψ l (b ⊗ₜ (c ⊗ₜ c')) = (l * antipode R c') ⊗ₜ (b * antipode R c) := by
      intro l b c c'
      simp [Ψ]
    show ∑ i ∈ (ℛ R x).index, comul ((ℛ R x).left i) * T ((ℛ R x).right i) =
      algebraMap R (A ⊗[R] A) (counit x)

    have step1 : ∑ i ∈ (ℛ R x).index, comul ((ℛ R x).left i) * T ((ℛ R x).right i) =
        ∑ i ∈ (ℛ R x).index, ∑ k ∈ (ℛ R ((ℛ R x).right i)).index,
          ((ℛ R x).left i ⊗ₜ (ℛ R ((ℛ R x).right i)).left k) * T ((ℛ R ((ℛ R x).right i)).right k) := by
      have h := sum_map_tmul_tmul_eq (R := R) (LinearMap.id : A →ₗ[R] A) (LinearMap.id : A →ₗ[R] A)
        (LinearMap.id : A →ₗ[R] A) x (repr := ℛ R x)
        (a₁ := fun i => ℛ R ((ℛ R x).left i)) (a₂ := fun i => ℛ R ((ℛ R x).right i))
      simp only [LinearMap.id_apply] at h
      symm
      calc ∑ i ∈ (ℛ R x).index, ∑ k ∈ (ℛ R ((ℛ R x).right i)).index,
            ((ℛ R x).left i ⊗ₜ (ℛ R ((ℛ R x).right i)).left k) * T ((ℛ R ((ℛ R x).right i)).right k)
          = ∑ i ∈ (ℛ R x).index, ∑ k ∈ (ℛ R ((ℛ R x).right i)).index,
            Φ ((ℛ R x).left i ⊗ₜ ((ℛ R ((ℛ R x).right i)).left k ⊗ₜ (ℛ R ((ℛ R x).right i)).right k)) := by
            simp only [hΦ]
        _ = Φ (∑ i ∈ (ℛ R x).index, ∑ k ∈ (ℛ R ((ℛ R x).right i)).index,
            ((ℛ R x).left i ⊗ₜ ((ℛ R ((ℛ R x).right i)).left k ⊗ₜ (ℛ R ((ℛ R x).right i)).right k))) := by
            simp only [map_sum]
        _ = Φ (∑ i ∈ (ℛ R x).index, ∑ j ∈ (ℛ R ((ℛ R x).left i)).index,
            ((ℛ R ((ℛ R x).left i)).left j ⊗ₜ ((ℛ R ((ℛ R x).left i)).right j ⊗ₜ (ℛ R x).right i))) := by
            rw [h]
        _ = ∑ i ∈ (ℛ R x).index, ∑ j ∈ (ℛ R ((ℛ R x).left i)).index,
            ((ℛ R ((ℛ R x).left i)).left j ⊗ₜ (ℛ R ((ℛ R x).left i)).right j) * T ((ℛ R x).right i) := by
            simp only [map_sum, hΦ]
        _ = ∑ i ∈ (ℛ R x).index, comul ((ℛ R x).left i) * T ((ℛ R x).right i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← (ℛ R ((ℛ R x).left i)).eq, Finset.sum_mul]
    rw [step1]

    have step2 : ∀ i ∈ (ℛ R x).index,
        ∑ k ∈ (ℛ R ((ℛ R x).right i)).index,
          ((ℛ R x).left i ⊗ₜ (ℛ R ((ℛ R x).right i)).left k) * T ((ℛ R ((ℛ R x).right i)).right k) =
        ((ℛ R x).left i * antipode R ((ℛ R x).right i)) ⊗ₜ (1 : A) := by
      intro i _
      set r := (ℛ R x).right i with hr
      set l := (ℛ R x).left i with hl
      have hT : ∀ k ∈ (ℛ R r).index,
          (l ⊗ₜ (ℛ R r).left k) * T ((ℛ R r).right k) =
            ∑ m ∈ (ℛ R ((ℛ R r).right k)).index,
              Ψ l ((ℛ R r).left k ⊗ₜ ((ℛ R ((ℛ R r).right k)).left m ⊗ₜ (ℛ R ((ℛ R r).right k)).right m)) := by
        intro k _
        simp only [hΨ]
        show (l ⊗ₜ[R] (ℛ R r).left k) *
            (TensorProduct.map (antipode R) (antipode R)
              ((TensorProduct.comm R A A) (comul ((ℛ R r).right k)))) = _
        rw [← (ℛ R ((ℛ R r).right k)).eq]
        simp only [map_sum, TensorProduct.comm_tmul, TensorProduct.map_tmul, Finset.mul_sum,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [Finset.sum_congr rfl hT]
      have h := sum_map_tmul_tmul_eq (R := R) (LinearMap.id : A →ₗ[R] A) (LinearMap.id : A →ₗ[R] A)
        (LinearMap.id : A →ₗ[R] A) r (repr := ℛ R r)
        (a₁ := fun k => ℛ R ((ℛ R r).left k)) (a₂ := fun k => ℛ R ((ℛ R r).right k))
      simp only [LinearMap.id_apply] at h
      have h2 : ∑ k ∈ (ℛ R r).index, ∑ m ∈ (ℛ R ((ℛ R r).right k)).index,
          Ψ l ((ℛ R r).left k ⊗ₜ ((ℛ R ((ℛ R r).right k)).left m ⊗ₜ (ℛ R ((ℛ R r).right k)).right m)) =
          ∑ k ∈ (ℛ R r).index, ∑ n ∈ (ℛ R ((ℛ R r).left k)).index,
            (l * antipode R ((ℛ R r).right k)) ⊗ₜ[R]
              ((ℛ R ((ℛ R r).left k)).left n * antipode R ((ℛ R ((ℛ R r).left k)).right n)) := by
        calc ∑ k ∈ (ℛ R r).index, ∑ m ∈ (ℛ R ((ℛ R r).right k)).index,
              Ψ l ((ℛ R r).left k ⊗ₜ ((ℛ R ((ℛ R r).right k)).left m ⊗ₜ (ℛ R ((ℛ R r).right k)).right m))
            = Ψ l (∑ k ∈ (ℛ R r).index, ∑ m ∈ (ℛ R ((ℛ R r).right k)).index,
                ((ℛ R r).left k ⊗ₜ ((ℛ R ((ℛ R r).right k)).left m ⊗ₜ (ℛ R ((ℛ R r).right k)).right m))) := by
                simp only [map_sum]
          _ = Ψ l (∑ k ∈ (ℛ R r).index, ∑ n ∈ (ℛ R ((ℛ R r).left k)).index,
                ((ℛ R ((ℛ R r).left k)).left n ⊗ₜ ((ℛ R ((ℛ R r).left k)).right n ⊗ₜ (ℛ R r).right k))) := by
                rw [h]
          _ = _ := by simp only [map_sum, hΨ]
      rw [h2]
      calc ∑ k ∈ (ℛ R r).index, ∑ n ∈ (ℛ R ((ℛ R r).left k)).index,
            (l * antipode R ((ℛ R r).right k)) ⊗ₜ[R]
              ((ℛ R ((ℛ R r).left k)).left n * antipode R ((ℛ R ((ℛ R r).left k)).right n))
          = ∑ k ∈ (ℛ R r).index,
              (l * antipode R ((ℛ R r).right k)) ⊗ₜ[R] (counit (R := R) ((ℛ R r).left k) • (1 : A)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← TensorProduct.tmul_sum, sum_mul_antipode_eq_smul]
        _ = ∑ k ∈ (ℛ R r).index,
              (l * antipode R (counit (R := R) ((ℛ R r).left k) • (ℛ R r).right k)) ⊗ₜ[R] (1 : A) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [map_smul, mul_smul_comm, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
        _ = (l * antipode R r) ⊗ₜ[R] (1 : A) := by
            rw [← TensorProduct.sum_tmul, ← Finset.mul_sum, ← map_sum, sum_counit_smul]
    rw [Finset.sum_congr rfl step2, ← TensorProduct.sum_tmul, sum_mul_antipode_eq_algebraMap_counit]
    rfl

theorem comul_antipode (a : A) :
    comul (antipode R a) =
      TensorProduct.map (antipode R) (antipode R) (TensorProduct.comm R A A (comul a)) :=
  congr($(comul_comp_antipode (R := R) (A := A)) a)

end ComulAntipode

section Main

variable {R : Type} [CommRing R] {L : Type} [CommRing L] [HopfAlgebra R L]
  {M : Type} [AddCommGroup M] [Module R M] [Module L M] [IsScalarTower R L M]
  (ρ : M →ₗ[R] M ⊗[R] L)

structure CoRepr (m : M) where
  {ι : Type}
  index : Finset ι
  left : ι → M
  right : ι → L
  eq : ∑ i ∈ index, left i ⊗ₜ[R] right i = ρ m

noncomputable def CoRepr.arb (m : M) : CoRepr ρ m where
  index := (TensorProduct.exists_finset (R := R) (ρ m)).choose
  left := Prod.fst
  right := Prod.snd
  eq := (TensorProduct.exists_finset (R := R) (ρ m)).choose_spec.symm

noncomputable def act : M ⊗[R] L →ₗ[R] M :=
  TensorProduct.lift ((Algebra.lsmul R R M : L →ₐ[R] Module.End R M).toLinearMap.flip)

omit ρ in
@[scoped simp] theorem act_tmul (m : M) (c : L) : act (R := R) (m ⊗ₜ[R] c) = c • m := by
  simp [act]

noncomputable def Hmap : (L ⊗[R] L) ⊗[R] (M ⊗[R] L) →ₗ[R] M ⊗[R] L :=
  TensorProduct.map (TensorProduct.lift ((Algebra.lsmul R R M : L →ₐ[R] Module.End R M).toLinearMap))
      (LinearMap.mul' R L) ∘ₗ
    (TensorProduct.tensorTensorTensorComm R L L M L).toLinearMap

omit ρ in
@[scoped simp] theorem Hmap_tmul (a b : L) (m : M) (c : L) :
    Hmap (R := R) ((a ⊗ₜ[R] b) ⊗ₜ[R] (m ⊗ₜ[R] c)) = (a • m) ⊗ₜ[R] (b * c) := by
  simp [Hmap]

noncomputable def P : M →ₗ[R] M := act ∘ₗ (antipode R (A := L)).lTensor M ∘ₗ ρ

theorem P_eq_sum {m : M} (𝓡 : CoRepr ρ m) :
    P ρ m = ∑ i ∈ 𝓡.index, antipode R (𝓡.right i) • 𝓡.left i := by
  simp only [P, LinearMap.comp_apply, ← 𝓡.eq, map_sum, LinearMap.lTensor_tmul, act_tmul]

variable (hcoassoc : (TensorProduct.assoc R M L L).toLinearMap ∘ₗ ρ.rTensor L ∘ₗ ρ =
      (Coalgebra.comul (R := R) (A := L)).lTensor M ∘ₗ ρ)
  (hcounit : (Coalgebra.counit (R := R) (A := L)).lTensor M ∘ₗ ρ = (TensorProduct.mk R M R).flip 1)
  (hmod : ∀ (c : L) (m : M), ρ (c • m) =
      TensorProduct.map (TensorProduct.lift ((Algebra.lsmul R R M : L →ₐ[R] Module.End R M).toLinearMap))
          (LinearMap.mul' R L)
        (TensorProduct.tensorTensorTensorComm R L L M L (Coalgebra.comul (R := R) c ⊗ₜ[R] ρ m)))

include hcounit in
theorem sum_counit_smul' {m : M} (𝓡 : CoRepr ρ m) :
    ∑ i ∈ 𝓡.index, counit (R := R) (𝓡.right i) • 𝓡.left i = m := by
  have h := congrArg (fun f : M →ₗ[R] M ⊗[R] R => TensorProduct.rid R M (f m)) hcounit
  simp only [LinearMap.comp_apply, ← 𝓡.eq, map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
    LinearMap.flip_apply, TensorProduct.mk_apply, one_smul] at h
  exact h

include hcoassoc in
theorem sum_tmul_tmul_eq' {m : M} (𝓡 : CoRepr ρ m) (a₁ : (i : 𝓡.ι) → CoRepr ρ (𝓡.left i))
    {κa₂ : 𝓡.ι → Type*} (a₂ : (i : 𝓡.ι) → Coalgebra.Repr R (𝓡.right i) (κa₂ i)) :
    ∑ i ∈ 𝓡.index, ∑ j ∈ (a₁ i).index,
        (a₁ i).left j ⊗ₜ[R] ((a₁ i).right j ⊗ₜ[R] 𝓡.right i) =
      ∑ i ∈ 𝓡.index, ∑ k ∈ (a₂ i).index,
        𝓡.left i ⊗ₜ[R] ((a₂ i).left k ⊗ₜ[R] (a₂ i).right k) := by
  have h := congrArg (fun f : M →ₗ[R] M ⊗[R] (L ⊗[R] L) => f m) hcoassoc
  simp only [LinearMap.comp_apply, ← 𝓡.eq, map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe] at h
  simp only [← (a₁ _).eq, ← (a₂ _).eq, TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
    TensorProduct.assoc_tmul] at h
  exact h

include hcoassoc hcounit in

theorem act_rTensor_P (m : M) : act ((P ρ).rTensor L (ρ m)) = m := by
  classical
  let 𝓡 := CoRepr.arb ρ m
  let Λ : M ⊗[R] (L ⊗[R] L) →ₗ[R] M :=
    act ∘ₗ (LinearMap.mul' R L ∘ₗ TensorProduct.map LinearMap.id (antipode R) ∘ₗ
      (TensorProduct.comm R L L).toLinearMap).lTensor M
  have hΛ : ∀ (x : M) (a b : L), Λ (x ⊗ₜ (a ⊗ₜ b)) = (b * antipode R a) • x := by
    intro x a b; simp [Λ]
  have key := congrArg Λ (sum_tmul_tmul_eq' ρ hcoassoc 𝓡 (fun i => CoRepr.arb ρ (𝓡.left i))
    (fun i => ℛ R (𝓡.right i)))
  simp only [map_sum, hΛ] at key
  calc act ((P ρ).rTensor L (ρ m))
      = ∑ i ∈ 𝓡.index, 𝓡.right i • P ρ (𝓡.left i) := by
        rw [← 𝓡.eq, map_sum, map_sum]
        simp only [LinearMap.rTensor_tmul, act_tmul]
    _ = ∑ i ∈ 𝓡.index, ∑ j ∈ (CoRepr.arb ρ (𝓡.left i)).index,
          (𝓡.right i * antipode R ((CoRepr.arb ρ (𝓡.left i)).right j)) •
            (CoRepr.arb ρ (𝓡.left i)).left j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [P_eq_sum ρ (CoRepr.arb ρ (𝓡.left i)), Finset.smul_sum]
        simp only [smul_smul]
    _ = ∑ i ∈ 𝓡.index, ∑ k ∈ (ℛ R (𝓡.right i)).index,
          ((ℛ R (𝓡.right i)).right k * antipode R ((ℛ R (𝓡.right i)).left k)) • 𝓡.left i := key
    _ = ∑ i ∈ 𝓡.index, counit (R := R) (𝓡.right i) • 𝓡.left i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_smul]
        simp only [mul_comm _ (antipode R _)]
        rw [sum_antipode_mul_eq_algebraMap_counit, algebraMap_smul]
    _ = m := sum_counit_smul' ρ hcounit 𝓡

include hmod in

theorem P_smul_of_coinv {n : M} (hn : ρ n = n ⊗ₜ[R] 1) (c : L) :
    P ρ (c • n) = counit (R := R) c • n := by
  classical
  have hρ : ρ (c • n) = ∑ k ∈ (ℛ R c).index, ((ℛ R c).left k • n) ⊗ₜ[R] (ℛ R c).right k := by
    rw [hmod, hn, ← (ℛ R c).eq, TensorProduct.sum_tmul, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  simp only [P, LinearMap.comp_apply, hρ, map_sum, LinearMap.lTensor_tmul, act_tmul, smul_smul]
  rw [← Finset.sum_smul]
  simp only [mul_comm (antipode R _)]
  rw [sum_mul_antipode_eq_smul, smul_assoc, one_smul]

include hcoassoc hmod in

theorem ρ_P (m : M) : ρ (P ρ m) = P ρ m ⊗ₜ[R] (1 : L) := by
  classical
  let 𝓡 := CoRepr.arb ρ m

  let g : L ⊗[R] (L ⊗[R] L) →ₗ[R] L ⊗[R] L :=
    TensorProduct.map (LinearMap.mul' R L ∘ₗ TensorProduct.map (antipode R) LinearMap.id ∘ₗ
        (TensorProduct.comm R L L).toLinearMap) (antipode R) ∘ₗ
      (TensorProduct.assoc R L L L).symm.toLinearMap
  have hg : ∀ c b b' : L, g (c ⊗ₜ (b ⊗ₜ b')) = (antipode R b * c) ⊗ₜ antipode R b' := by
    intro c b b'; simp [g]
  let Θ : M ⊗[R] (L ⊗[R] (L ⊗[R] L)) →ₗ[R] M ⊗[R] L :=
    TensorProduct.map (TensorProduct.lift ((Algebra.lsmul R R M : L →ₐ[R] Module.End R M).toLinearMap))
        LinearMap.id ∘ₗ
      (TensorProduct.assoc R L M L).symm.toLinearMap ∘ₗ
      (TensorProduct.comm R (M ⊗[R] L) L).toLinearMap ∘ₗ
      (TensorProduct.assoc R M L L).symm.toLinearMap ∘ₗ g.lTensor M
  have hΘ : ∀ (x : M) (c b b' : L),
      Θ (x ⊗ₜ (c ⊗ₜ (b ⊗ₜ b'))) = (antipode R b' • x) ⊗ₜ (antipode R b * c) := by
    intro x c b b'
    simp only [Θ, LinearMap.comp_apply, LinearMap.lTensor_tmul, hg]
    simp

  have h0 : ρ (P ρ m) = ∑ i ∈ 𝓡.index, ∑ j ∈ (CoRepr.arb ρ (𝓡.left i)).index,
      ∑ k ∈ (ℛ R (𝓡.right i)).index,
        Θ ((CoRepr.arb ρ (𝓡.left i)).left j ⊗ₜ ((CoRepr.arb ρ (𝓡.left i)).right j ⊗ₜ
          ((ℛ R (𝓡.right i)).left k ⊗ₜ (ℛ R (𝓡.right i)).right k))) := by
    rw [P_eq_sum ρ 𝓡, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hmod, comul_antipode, ← (ℛ R (𝓡.right i)).eq, ← (CoRepr.arb ρ (𝓡.left i)).eq]
    simp only [map_sum, TensorProduct.comm_tmul, TensorProduct.map_tmul, TensorProduct.sum_tmul,
      TensorProduct.tmul_sum, hΘ]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    simp

  have key1 := congrArg (Θ ∘ₗ (LinearMap.lTensor M (LinearMap.lTensor L (comul (R := R) (A := L)))))
    (sum_tmul_tmul_eq' ρ hcoassoc 𝓡 (fun i => CoRepr.arb ρ (𝓡.left i)) (fun i => ℛ R (𝓡.right i)))
  simp only [LinearMap.comp_apply, map_sum, LinearMap.lTensor_tmul] at key1
  have h1 : ρ (P ρ m) = ∑ i ∈ 𝓡.index, ∑ k ∈ (ℛ R (𝓡.right i)).index,
      Θ (𝓡.left i ⊗ₜ ((ℛ R (𝓡.right i)).left k ⊗ₜ comul ((ℛ R (𝓡.right i)).right k))) := by
    rw [h0, ← key1]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← (ℛ R (𝓡.right i)).eq, TensorProduct.tmul_sum, TensorProduct.tmul_sum, map_sum]

  have h2 : ∀ i ∈ 𝓡.index, ∑ k ∈ (ℛ R (𝓡.right i)).index,
      Θ (𝓡.left i ⊗ₜ ((ℛ R (𝓡.right i)).left k ⊗ₜ comul ((ℛ R (𝓡.right i)).right k))) =
      (antipode R (𝓡.right i) • 𝓡.left i) ⊗ₜ (1 : L) := by
    intro i _
    set r := 𝓡.right i
    set x := 𝓡.left i
    have hc := sum_map_tmul_tmul_eq (R := R) (LinearMap.id : L →ₗ[R] L) (LinearMap.id : L →ₗ[R] L)
      (LinearMap.id : L →ₗ[R] L) r (repr := ℛ R r)
      (a₁ := fun k => ℛ R ((ℛ R r).left k)) (a₂ := fun k => ℛ R ((ℛ R r).right k))
    simp only [LinearMap.id_apply] at hc
    have hc' := congrArg (Θ ∘ₗ TensorProduct.mk R M (L ⊗[R] (L ⊗[R] L)) x) hc
    simp only [LinearMap.comp_apply, map_sum, TensorProduct.mk_apply, hΘ] at hc'
    calc ∑ k ∈ (ℛ R r).index, Θ (x ⊗ₜ ((ℛ R r).left k ⊗ₜ comul ((ℛ R r).right k)))
        = ∑ k ∈ (ℛ R r).index, ∑ n ∈ (ℛ R ((ℛ R r).right k)).index,
            (antipode R ((ℛ R ((ℛ R r).right k)).right n) • x) ⊗ₜ[R]
              (antipode R ((ℛ R ((ℛ R r).right k)).left n) * (ℛ R r).left k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← (ℛ R ((ℛ R r).right k)).eq]
          simp only [TensorProduct.tmul_sum, map_sum, hΘ]
      _ = ∑ k ∈ (ℛ R r).index, ∑ n ∈ (ℛ R ((ℛ R r).left k)).index,
            (antipode R ((ℛ R r).right k) • x) ⊗ₜ[R]
              (antipode R ((ℛ R ((ℛ R r).left k)).right n) * (ℛ R ((ℛ R r).left k)).left n) := hc'
      _ = ∑ k ∈ (ℛ R r).index,
            (antipode R ((ℛ R r).right k) • x) ⊗ₜ[R] algebraMap R L (counit (R := R) ((ℛ R r).left k)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← TensorProduct.tmul_sum]
          simp only [mul_comm (antipode R _)]
          rw [sum_mul_antipode_eq_algebraMap_counit]
      _ = ∑ k ∈ (ℛ R r).index,
            (antipode R (counit (R := R) ((ℛ R r).left k) • (ℛ R r).right k) • x) ⊗ₜ[R] (1 : L) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, map_smul, smul_assoc]
      _ = (antipode R r • x) ⊗ₜ[R] (1 : L) := by
          rw [← TensorProduct.sum_tmul, ← Finset.sum_smul, ← map_sum, sum_counit_smul]
  rw [h1, Finset.sum_congr rfl h2, ← TensorProduct.sum_tmul, ← P_eq_sum ρ 𝓡]

include hmod in
theorem ρ_smul_coinv {n : M} (hn : ρ n = n ⊗ₜ[R] 1) (c : L) :
    ρ (c • n) = ∑ k ∈ (ℛ R c).index, ((ℛ R c).left k • n) ⊗ₜ[R] (ℛ R c).right k := by
  rw [hmod, hn, ← (ℛ R c).eq, TensorProduct.sum_tmul, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

end Main

end H1
p2m_reactivate "P2MW.S_HopfAlgebra_bijective_lift_coinvariants_and_bijective_mkQ_of_isHopfModule.H1"

open H1 Coalgebra HopfAlgebra in
theorem solution
    {R : Type} [CommRing R] {L : Type} [CommRing L] [HopfAlgebra R L]
    {M : Type} [AddCommGroup M] [Module R M] [Module L M] [IsScalarTower R L M]
    (ρ : M →ₗ[R] M ⊗[R] L)
    (hcoassoc : (TensorProduct.assoc R M L L).toLinearMap ∘ₗ ρ.rTensor L ∘ₗ ρ =
      (Coalgebra.comul (R := R) (A := L)).lTensor M ∘ₗ ρ)
    (hcounit : (Coalgebra.counit (R := R) (A := L)).lTensor M ∘ₗ ρ = (TensorProduct.mk R M R).flip 1)
    (hmod : ∀ (c : L) (m : M), ρ (c • m) =
      TensorProduct.map (TensorProduct.lift ((Algebra.lsmul R R M : L →ₐ[R] Module.End R M).toLinearMap))
          (LinearMap.mul' R L)
        (TensorProduct.tensorTensorTensorComm R L L M L (Coalgebra.comul (R := R) c ⊗ₜ[R] ρ m))) :
    let Mco : Submodule R M := LinearMap.ker (ρ - (TensorProduct.mk R M L).flip (1 : L))
    Function.Bijective
        (TensorProduct.lift
          (((Algebra.lsmul R R M : L →ₐ[R] Module.End R M).toLinearMap.flip) ∘ₗ Mco.subtype) :
          Mco ⊗[R] L → M) ∧
      Function.Bijective (fun m : Mco =>
        (Submodule.Quotient.mk (m : M) :
          M ⧸ ((RingHom.ker (Bialgebra.counitAlgHom R L)) • (⊤ : Submodule L M)))) := by
  intro Mco
  classical
  have hMco : ∀ {m : M}, m ∈ Mco ↔ ρ m = m ⊗ₜ[R] (1 : L) := by
    intro m
    simp only [Mco, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      sub_eq_zero]
  have hP : ∀ m, P ρ m ∈ Mco := fun m => hMco.2 (ρ_P ρ hcoassoc hmod m)
  let P' : M →ₗ[R] Mco := LinearMap.codRestrict Mco (P ρ) hP
  have hP' : ∀ m, (P' m : M) = P ρ m := fun m => rfl
  let act' : Mco ⊗[R] L →ₗ[R] M := TensorProduct.lift
    (((Algebra.lsmul R R M : L →ₐ[R] Module.End R M).toLinearMap.flip) ∘ₗ Mco.subtype)
  have hact' : ∀ (n : Mco) (c : L), act' (n ⊗ₜ c) = c • (n : M) := by
    intro n c; simp [act']
  let Q : M →ₗ[R] Mco ⊗[R] L := P'.rTensor L ∘ₗ ρ

  have h1 : ∀ m, act' (Q m) = m := by
    intro m
    have hcomp : act' ∘ₗ P'.rTensor L = act ∘ₗ (P ρ).rTensor L := by
      apply TensorProduct.ext'
      intro x c
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, hact', hP', act_tmul]
    calc act' (Q m) = (act' ∘ₗ P'.rTensor L) (ρ m) := rfl
      _ = act ((P ρ).rTensor L (ρ m)) := by rw [hcomp]; rfl
      _ = m := act_rTensor_P ρ hcoassoc hcounit m

  have h2 : ∀ x, Q (act' x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul n c =>
      rw [hact']
      have hn : ρ (n : M) = (n : M) ⊗ₜ[R] (1 : L) := hMco.1 n.2
      show (P'.rTensor L) (ρ (c • (n : M))) = n ⊗ₜ c
      rw [ρ_smul_coinv ρ hmod hn, map_sum]
      simp only [LinearMap.rTensor_tmul]
      have hk : ∀ k, P' ((ℛ R c).left k • (n : M)) = counit (R := R) ((ℛ R c).left k) • n := by
        intro k
        apply Subtype.ext
        rw [hP', P_smul_of_coinv ρ hmod hn, Submodule.coe_smul]
      simp only [hk, TensorProduct.smul_tmul]
      rw [← TensorProduct.tmul_sum, sum_counit_smul]
  refine ⟨?_, ?_⟩
  ·
    change Function.Bijective act'
    refine ⟨fun x y hxy => ?_, fun m => ⟨Q m, h1 m⟩⟩
    have := congrArg Q hxy
    rwa [h2, h2] at this
  ·
    have hsmul_act : ∀ (c : L) (x : Mco ⊗[R] L),
        c • act' x = act' ((LinearMap.mulLeft R c).lTensor Mco x) := by
      intro c x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, smul_add, hx, hy]
      | tmul n l =>
        simp only [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, hact', smul_smul]

    let χ : M →ₗ[R] Mco :=
      (TensorProduct.rid R Mco).toLinearMap ∘ₗ (counit (R := R) (A := L)).lTensor Mco ∘ₗ Q
    have hχ1 : ∀ n : Mco, χ (n : M) = n := by
      intro n
      have : (n : M) = act' (n ⊗ₜ (1 : L)) := by rw [hact', one_smul]
      show TensorProduct.rid R Mco ((counit (R := R) (A := L)).lTensor Mco (Q (n : M))) = n
      rw [this, h2]
      simp
    have hχ2 : ∀ m ∈ (RingHom.ker (Bialgebra.counitAlgHom R L)) • (⊤ : Submodule L M), χ m = 0 := by
      intro m hm
      refine Submodule.smul_induction_on hm (fun c hc m _ => ?_) (fun x y hx hy => ?_)
      · have hc' : counit (R := R) c = 0 := hc
        show TensorProduct.rid R Mco ((counit (R := R) (A := L)).lTensor Mco (Q (c • m))) = 0
        rw [← h1 m, hsmul_act, h2, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        have : (counit (R := R) (A := L)) ∘ₗ LinearMap.mulLeft R c = 0 := by
          ext l
          simp [hc']
        rw [this]
        simp
      · rw [map_add, hx, hy, add_zero]
    constructor
    · intro n₁ n₂ h
      have h' := (Submodule.Quotient.eq _).1 h
      have := hχ2 _ h'
      rw [map_sub, hχ1, hχ1, sub_eq_zero] at this
      exact this
    · intro q
      induction q using Submodule.Quotient.induction_on with
      | H m =>

        have key : ∀ x : Mco ⊗[R] L, ∃ n : Mco,
            (Submodule.Quotient.mk (act' x) :
              M ⧸ ((RingHom.ker (Bialgebra.counitAlgHom R L)) • (⊤ : Submodule L M))) =
            Submodule.Quotient.mk (n : M) := by
          intro x
          induction x using TensorProduct.induction_on with
          | zero => exact ⟨0, by simp⟩
          | add x y hx hy =>
            obtain ⟨n₁, h₁⟩ := hx
            obtain ⟨n₂, h₂⟩ := hy
            refine ⟨n₁ + n₂, ?_⟩
            rw [map_add, Submodule.Quotient.mk_add, h₁, h₂, Submodule.coe_add, Submodule.Quotient.mk_add]
          | tmul n c =>
            refine ⟨counit (R := R) c • n, ?_⟩
            rw [hact', Submodule.Quotient.eq, Submodule.coe_smul]
            have : c • (n : M) - counit (R := R) c • (n : M) =
                (c - algebraMap R L (counit (R := R) c)) • (n : M) := by
              rw [sub_smul, algebraMap_smul]
            rw [this]
            refine Submodule.smul_mem_smul ?_ Submodule.mem_top
            show Bialgebra.counitAlgHom R L (c - algebraMap R L (counit c)) = 0
            rw [map_sub, AlgHom.commutes]
            exact sub_self _
        obtain ⟨n, hn⟩ := key (Q m)
        rw [h1] at hn
        exact ⟨n, hn.symm⟩

end S_HopfAlgebra_bijective_lift_coinvariants_and_bijective_mkQ_of_isHopfModule
end P2MW
export P2MW.S_HopfAlgebra_bijective_lift_coinvariants_and_bijective_mkQ_of_isHopfModule (solution)

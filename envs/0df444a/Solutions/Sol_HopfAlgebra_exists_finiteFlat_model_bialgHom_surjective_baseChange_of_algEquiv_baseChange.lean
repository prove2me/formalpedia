-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/9249ff5a-3eb9-5d24-b6ea-e739dce9a132

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange

set_option autoImplicit false

open scoped TensorProduct

universe u v

noncomputable section

namespace SupModelProof

section QuotSyn

variable {A : Type*} [CommRing A]

def QS (I : Ideal A) : Type _ := A ⧸ I

scoped instance QS.instCommRing (I : Ideal A) : CommRing (QS I) := inferInstanceAs (CommRing (A ⧸ I))

p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS"
scoped instance QS.instAlgebra {R : Type*} [CommRing R] [Algebra R A] (I : Ideal A) :
    Algebra R (QS I) := inferInstanceAs (Algebra R (A ⧸ I))

p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS"

def QS.mk (R : Type*) [CommRing R] [Algebra R A] (I : Ideal A) : A →ₐ[R] QS I :=
  Ideal.Quotient.mkₐ R I

theorem QS.mk_surjective {R : Type*} [CommRing R] [Algebra R A] (I : Ideal A) :
    Function.Surjective (QS.mk R I) :=
  Ideal.Quotient.mkₐ_surjective R I

theorem QS.mk_eq_zero_iff {R : Type*} [CommRing R] [Algebra R A] (I : Ideal A) (x : A) :
    QS.mk R I x = 0 ↔ x ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem

def QS.lift (R : Type*) [CommRing R] [Algebra R A] (I : Ideal A) {B : Type*} [Semiring B]
    [Algebra R B] (f : A →ₐ[R] B) (hf : ∀ a ∈ I, f a = 0) : QS I →ₐ[R] B :=
  Ideal.Quotient.liftₐ I f hf

@[scoped simp] theorem QS.lift_mk {R : Type*} [CommRing R] [Algebra R A] (I : Ideal A) {B : Type*}
    [Semiring B] [Algebra R B] (f : A →ₐ[R] B) (hf : ∀ a ∈ I, f a = 0) (x : A) :
    QS.lift R I f hf (QS.mk R I x) = f x := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS"
theorem QS.lift_injective {R : Type*} [CommRing R] [Algebra R A] (I : Ideal A) {B : Type*}
    [Ring B] [Algebra R B] (f : A →ₐ[R] B) (hf : ∀ a, a ∈ I ↔ f a = 0) :
    Function.Injective (QS.lift R I f (fun a ha => (hf a).mp ha)) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := QS.mk_surjective (R := R) I x
  obtain ⟨b, rfl⟩ := QS.mk_surjective (R := R) I y
  rw [QS.lift_mk, QS.lift_mk] at hxy
  rw [← sub_eq_zero, ← map_sub, QS.mk_eq_zero_iff, hf, map_sub, hxy, sub_self]

theorem QS.moduleFinite (R : Type*) [CommRing R] [Algebra R A] (I : Ideal A) [Module.Finite R A] :
    Module.Finite R (QS I) :=
  Module.Finite.of_surjective (QS.mk R I).toLinearMap (QS.mk_surjective (R := R) I)

end QuotSyn
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS"

section HopfQuot

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A]

variable (R A) in

def antipodeAlgHom : A →ₐ[R] A where
  toFun := HopfAlgebra.antipode R
  map_one' := HopfAlgebra.antipode_one
  map_mul' a b := by rw [HopfAlgebra.antipode_mul, mul_comm]
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one]

@[scoped simp] theorem antipodeAlgHom_apply (a : A) : antipodeAlgHom R A a = HopfAlgebra.antipode R a :=
  rfl

theorem lift_antipode_id_apply (z : A ⊗[R] A) :
    (Algebra.TensorProduct.lift (antipodeAlgHom R A) (AlgHom.id R A)
        fun _ _ => Commute.all _ _) z
      = LinearMap.mul' R A ((HopfAlgebra.antipode R (A := A)).rTensor A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [antipodeAlgHom_apply]

theorem lift_id_antipode_apply (z : A ⊗[R] A) :
    (Algebra.TensorProduct.lift (AlgHom.id R A) (antipodeAlgHom R A)
        fun _ _ => Commute.all _ _) z
      = LinearMap.mul' R A ((HopfAlgebra.antipode R (A := A)).lTensor A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [antipodeAlgHom_apply]

theorem lift_antipode_id_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (antipodeAlgHom R A) (AlgHom.id R A)
        fun _ _ => Commute.all _ _).comp (Bialgebra.comulAlgHom R A)
      = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A) := by
  refine AlgHom.ext fun x => ?_
  rw [AlgHom.comp_apply, lift_antipode_id_apply, Bialgebra.comulAlgHom_apply,
    HopfAlgebra.mul_antipode_rTensor_comul_apply]
  simp [Algebra.ofId_apply]

theorem lift_id_antipode_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (AlgHom.id R A) (antipodeAlgHom R A)
        fun _ _ => Commute.all _ _).comp (Bialgebra.comulAlgHom R A)
      = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A) := by
  refine AlgHom.ext fun x => ?_
  rw [AlgHom.comp_apply, lift_id_antipode_apply, Bialgebra.comulAlgHom_apply,
    HopfAlgebra.mul_antipode_lTensor_comul_apply]
  simp [Algebra.ofId_apply]

theorem convMul_comp_antipodeAlgHom {T : Type*} [CommSemiring T] [Algebra R T]
    (φ : A →ₐ[R] T) :
    WithConv.toConv φ * WithConv.toConv (φ.comp (antipodeAlgHom R A)) = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (WithConv.toConv φ * WithConv.toConv (φ.comp (antipodeAlgHom R A))) x =
    (1 : WithConv (A →ₐ[R] T)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv]
  have : ∀ z : A ⊗[R] A, Algebra.TensorProduct.lift φ (φ.comp (antipodeAlgHom R A))
      (fun _ _ => .all _ _) z = φ (LinearMap.mul' R A ((HopfAlgebra.antipode R).lTensor A z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [LinearMap.lTensor_tmul]
    | add x y hx hy => simp [map_add, hx, hy]
  rw [this, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]

theorem comp_antipodeAlgHom_convMul {T : Type*} [CommSemiring T] [Algebra R T]
    (φ : A →ₐ[R] T) :
    WithConv.toConv (φ.comp (antipodeAlgHom R A)) * WithConv.toConv φ = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (WithConv.toConv (φ.comp (antipodeAlgHom R A)) * WithConv.toConv φ) x =
    (1 : WithConv (A →ₐ[R] T)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv]
  have : ∀ z : A ⊗[R] A, Algebra.TensorProduct.lift (φ.comp (antipodeAlgHom R A)) φ
      (fun _ _ => .all _ _) z = φ (LinearMap.mul' R A ((HopfAlgebra.antipode R).rTensor A z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [LinearMap.rTensor_tmul]
    | add x y hx hy => simp [map_add, hx, hy]
  rw [this, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]

theorem bialgHom_comp_antipodeAlgHom {B : Type*} [CommRing B] [HopfAlgebra R B]
    (f : A →ₐc[R] B) :
    (f : A →ₐ[R] B).comp (antipodeAlgHom R A) = (antipodeAlgHom R B).comp (f : A →ₐ[R] B) := by

  have h1 : WithConv.toConv (f : A →ₐ[R] B) *
      WithConv.toConv ((f : A →ₐ[R] B).comp (antipodeAlgHom R A)) = 1 :=
    convMul_comp_antipodeAlgHom (f : A →ₐ[R] B)
  have h2 : WithConv.toConv ((antipodeAlgHom R B).comp (f : A →ₐ[R] B)) *
      WithConv.toConv (f : A →ₐ[R] B) = 1 := by
    have h := comp_antipodeAlgHom_convMul (AlgHom.id R B)
    have h' := congrArg (fun g : WithConv (B →ₐ[R] B) => WithConv.toConv (g.ofConv.comp
      (f : A →ₐ[R] B))) h
    rw [AlgHom.convMul_comp_bialgHom_distrib, WithConv.toConv_ofConv] at h'
    simp only [AlgHom.id_comp] at h'
    rw [h']
    refine WithConv.ext (AlgHom.ext fun x => ?_)
    change algebraMap R B (Coalgebra.counit (f x)) = algebraMap R B (Coalgebra.counit x)
    rw [CoalgHomClass.counit_comp_apply]
  have : WithConv.toConv ((antipodeAlgHom R B).comp (f : A →ₐ[R] B)) =
      WithConv.toConv ((f : A →ₐ[R] B).comp (antipodeAlgHom R A)) := by
    calc WithConv.toConv ((antipodeAlgHom R B).comp (f : A →ₐ[R] B))
        = WithConv.toConv ((antipodeAlgHom R B).comp (f : A →ₐ[R] B)) *
            (WithConv.toConv (f : A →ₐ[R] B) *
              WithConv.toConv ((f : A →ₐ[R] B).comp (antipodeAlgHom R A))) := by
          rw [h1, mul_one]
      _ = WithConv.toConv ((f : A →ₐ[R] B).comp (antipodeAlgHom R A)) := by
          rw [← mul_assoc, h2, one_mul]
  exact (WithConv.toConv_injective this).symm

variable (R) in

structure IsHopfIdeal' (I : Ideal A) : Prop where
  counit_eq_zero : ∀ x ∈ I, Coalgebra.counit (R := R) x = 0
  map_comul_eq_zero : ∀ x ∈ I,
    Algebra.TensorProduct.map (QS.mk R I) (QS.mk R I) (Coalgebra.comul (R := R) x) = 0
  antipode_mem : ∀ x ∈ I, HopfAlgebra.antipode R x ∈ I

def HQ (I : Ideal A) (_hI : IsHopfIdeal' R I) : Type _ := A ⧸ I

variable (I : Ideal A) (hI : IsHopfIdeal' R I)

scoped instance HQ.instCommRing : CommRing (HQ I hI) := inferInstanceAs (CommRing (A ⧸ I))
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ"
scoped instance HQ.instAlgebra : Algebra R (HQ I hI) := inferInstanceAs (Algebra R (A ⧸ I))

p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ"

def HQ.mkₐ : A →ₐ[R] HQ I hI := Ideal.Quotient.mkₐ R I

theorem HQ.mkₐ_surjective : Function.Surjective (HQ.mkₐ I hI) :=
  Ideal.Quotient.mkₐ_surjective R I

theorem HQ.mkₐ_eq_zero_iff (x : A) : HQ.mkₐ I hI x = 0 ↔ x ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem

theorem HQ.algHom_ext {B : Type*} [Semiring B] [Algebra R B] {f g : HQ I hI →ₐ[R] B}
    (h : f.comp (HQ.mkₐ I hI) = g.comp (HQ.mkₐ I hI)) : f = g :=
  Ideal.Quotient.algHom_ext R h

def HQ.liftₐ {B : Type*} [Semiring B] [Algebra R B] (f : A →ₐ[R] B) (hf : ∀ a ∈ I, f a = 0) :
    HQ I hI →ₐ[R] B :=
  Ideal.Quotient.liftₐ I f hf

@[scoped simp] theorem HQ.liftₐ_mkₐ {B : Type*} [Semiring B] [Algebra R B] (f : A →ₐ[R] B)
    (hf : ∀ a ∈ I, f a = 0) (x : A) : HQ.liftₐ I hI f hf (HQ.mkₐ I hI x) = f x := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ"
theorem HQ.liftₐ_comp {B : Type*} [Semiring B] [Algebra R B] (f : A →ₐ[R] B)
    (hf : ∀ a ∈ I, f a = 0) : (HQ.liftₐ I hI f hf).comp (HQ.mkₐ I hI) = f :=
  AlgHom.ext fun _ => rfl

theorem HQ.liftₐ_injective {B : Type*} [Ring B] [Algebra R B] (f : A →ₐ[R] B)
    (hf : ∀ a, a ∈ I ↔ f a = 0) :
    Function.Injective (HQ.liftₐ I hI f (fun a ha => (hf a).mp ha)) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := HQ.mkₐ_surjective I hI x
  obtain ⟨b, rfl⟩ := HQ.mkₐ_surjective I hI y
  rw [HQ.liftₐ_mkₐ, HQ.liftₐ_mkₐ] at hxy
  rw [← sub_eq_zero, ← map_sub, HQ.mkₐ_eq_zero_iff, hf, map_sub, hxy, sub_self]

local notation "C" => HQ I hI
local notation "π" => HQ.mkₐ I hI

def HQ.counit : C →ₐ[R] R :=
  HQ.liftₐ I hI (Bialgebra.counitAlgHom R A) fun x hx => hI.counit_eq_zero x hx

theorem HQ.counit_comp_mk : (HQ.counit I hI).comp π = Bialgebra.counitAlgHom R A :=
  HQ.liftₐ_comp _ _ _ _

def HQ.comul : C →ₐ[R] C ⊗[R] C :=
  HQ.liftₐ I hI ((Algebra.TensorProduct.map π π).comp (Bialgebra.comulAlgHom R A))
    fun x hx => hI.map_comul_eq_zero x hx

theorem HQ.comul_comp_mk :
    (HQ.comul I hI).comp π = (Algebra.TensorProduct.map π π).comp (Bialgebra.comulAlgHom R A) :=
  HQ.liftₐ_comp _ _ _ _

theorem HQ.comul_mk (x : A) :
    HQ.comul I hI (π x) = TensorProduct.map (π).toLinearMap (π).toLinearMap
      (Coalgebra.comul (R := R) x) := rfl

theorem HQ.comul_rTensor_counit :
    (Algebra.TensorProduct.map (HQ.counit I hI) (AlgHom.id R C)).comp (HQ.comul I hI)
      = (Algebra.TensorProduct.lid R C).symm.toAlgHom := by
  refine HQ.algHom_ext I hI ?_
  rw [AlgHom.comp_assoc, HQ.comul_comp_mk, ← AlgHom.comp_assoc,
    ← Algebra.TensorProduct.map_comp, HQ.counit_comp_mk, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  change TensorProduct.map (Bialgebra.counitAlgHom R A).toLinearMap (π).toLinearMap
      (Coalgebra.comul (R := R) x) = (Algebra.TensorProduct.lid R C).symm (π x)
  rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply,
    show ((Bialgebra.counitAlgHom R A).toLinearMap.rTensor A) (Coalgebra.comul (R := R) x)
      = (1 : R) ⊗ₜ[R] x from Coalgebra.rTensor_counit_comul (R := R) x]
  simp

theorem HQ.comul_lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id R C) (HQ.counit I hI)).comp (HQ.comul I hI)
      = (Algebra.TensorProduct.rid R R C).symm.toAlgHom := by
  refine HQ.algHom_ext I hI ?_
  rw [AlgHom.comp_assoc, HQ.comul_comp_mk, ← AlgHom.comp_assoc,
    ← Algebra.TensorProduct.map_comp, HQ.counit_comp_mk, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  change TensorProduct.map (π).toLinearMap (Bialgebra.counitAlgHom R A).toLinearMap
      (Coalgebra.comul (R := R) x) = (Algebra.TensorProduct.rid R R C).symm (π x)
  rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply,
    show ((Bialgebra.counitAlgHom R A).toLinearMap.lTensor A) (Coalgebra.comul (R := R) x)
      = x ⊗ₜ[R] (1 : R) from Coalgebra.lTensor_counit_comul (R := R) x]
  simp

theorem HQ.comul_coassoc :
    (Algebra.TensorProduct.assoc R R R C C C).toAlgHom.comp
        ((Algebra.TensorProduct.map (HQ.comul I hI) (AlgHom.id R C)).comp (HQ.comul I hI))
      = (Algebra.TensorProduct.map (AlgHom.id R C) (HQ.comul I hI)).comp (HQ.comul I hI) := by
  refine HQ.algHom_ext I hI ?_
  refine AlgHom.ext fun x => ?_
  have hΔCπ : (HQ.comul I hI).toLinearMap ∘ₗ (π).toLinearMap
      = TensorProduct.map (π).toLinearMap (π).toLinearMap ∘ₗ Coalgebra.comul (R := R) (A := A) :=
    LinearMap.ext fun y => rfl
  have hassoc_nat : ∀ z : (A ⊗[R] A) ⊗[R] A,
      (Algebra.TensorProduct.assoc R R R C C C)
        (TensorProduct.map (TensorProduct.map (π).toLinearMap (π).toLinearMap)
          (π).toLinearMap z)
        = TensorProduct.map (π).toLinearMap
            (TensorProduct.map (π).toLinearMap (π).toLinearMap)
            ((Algebra.TensorProduct.assoc R R R A A A) z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul xy c =>
      induction xy using TensorProduct.induction_on with
      | zero => simp only [map_zero, TensorProduct.zero_tmul]
      | tmul x y => simp only [TensorProduct.map_tmul, Algebra.TensorProduct.assoc_tmul]
      | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
    | add u v hu hv => simp only [map_add, hu, hv]
  have hLHS :
      TensorProduct.map (HQ.comul I hI).toLinearMap (LinearMap.id (M := C))
          ∘ₗ TensorProduct.map (π).toLinearMap (π).toLinearMap
        = TensorProduct.map (TensorProduct.map (π).toLinearMap (π).toLinearMap) (π).toLinearMap
          ∘ₗ TensorProduct.map (Coalgebra.comul (R := R) (A := A)) LinearMap.id := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hΔCπ, LinearMap.id_comp,
      LinearMap.comp_id]
  have hRHS :
      TensorProduct.map (LinearMap.id (M := C)) (HQ.comul I hI).toLinearMap
          ∘ₗ TensorProduct.map (π).toLinearMap (π).toLinearMap
        = TensorProduct.map (π).toLinearMap (TensorProduct.map (π).toLinearMap (π).toLinearMap)
          ∘ₗ TensorProduct.map LinearMap.id (Coalgebra.comul (R := R) (A := A)) := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp, hΔCπ,
      LinearMap.comp_id]
  have hLHSx := DFunLike.congr_fun hLHS (Coalgebra.comul (R := R) x)
  have hRHSx := DFunLike.congr_fun hRHS (Coalgebra.comul (R := R) x)
  simp only [LinearMap.comp_apply] at hLHSx hRHSx
  change (Algebra.TensorProduct.assoc R R R C C C)
      (TensorProduct.map (HQ.comul I hI).toLinearMap (LinearMap.id (M := C))
        (HQ.comul I hI (π x))) =
      TensorProduct.map (LinearMap.id (M := C)) (HQ.comul I hI).toLinearMap (HQ.comul I hI (π x))
  rw [HQ.comul_mk, hLHSx, hRHSx, hassoc_nat]
  exact congrArg _ (DFunLike.congr_fun (Coalgebra.coassoc (R := R) (A := A)) x)

scoped instance HQ.instBialgebra : Bialgebra R C :=
  Bialgebra.ofAlgHom (HQ.comul I hI) (HQ.counit I hI)
    (HQ.comul_coassoc I hI) (HQ.comul_rTensor_counit I hI) (HQ.comul_lTensor_counit I hI)

p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ"
theorem HQ.comulAlgHom_eq : Bialgebra.comulAlgHom R C = HQ.comul I hI := rfl
theorem HQ.counitAlgHom_eq : Bialgebra.counitAlgHom R C = HQ.counit I hI := rfl

theorem HQ.comul_def (y : C) :
    Coalgebra.comul (R := R) y = HQ.comul I hI y := rfl
theorem HQ.counit_def (y : C) :
    Coalgebra.counit (R := R) y = HQ.counit I hI y := rfl

def HQ.antipode : C →ₐ[R] C :=
  HQ.liftₐ I hI ((π).comp (antipodeAlgHom R A)) fun x hx => by
    change π (HopfAlgebra.antipode R x) = 0
    rw [HQ.mkₐ_eq_zero_iff]
    exact hI.antipode_mem x hx

theorem HQ.antipode_comp_mk :
    (HQ.antipode I hI).comp π = (π).comp (antipodeAlgHom R A) :=
  HQ.liftₐ_comp _ _ _ _

theorem HQ.lift_map_mk_naturality_rTensor :
    (Algebra.TensorProduct.lift (HQ.antipode I hI) (AlgHom.id R C)
          fun _ _ => Commute.all _ _).comp (Algebra.TensorProduct.map π π)
      = (π).comp (Algebra.TensorProduct.lift (antipodeAlgHom R A) (AlgHom.id R A)
          fun _ _ => Commute.all _ _) := by
  refine AlgHom.toLinearMap_injective (TensorProduct.ext' fun x y => ?_)
  simp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id, map_mul,
    ← AlgHom.comp_apply (HQ.antipode I hI), HQ.antipode_comp_mk]

theorem HQ.lift_map_mk_naturality_lTensor :
    (Algebra.TensorProduct.lift (AlgHom.id R C) (HQ.antipode I hI)
          fun _ _ => Commute.all _ _).comp (Algebra.TensorProduct.map π π)
      = (π).comp (Algebra.TensorProduct.lift (AlgHom.id R A) (antipodeAlgHom R A)
          fun _ _ => Commute.all _ _) := by
  refine AlgHom.toLinearMap_injective (TensorProduct.ext' fun x y => ?_)
  simp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id, map_mul,
    ← AlgHom.comp_apply (HQ.antipode I hI), HQ.antipode_comp_mk]

theorem HQ.mul_antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (HQ.antipode I hI) (AlgHom.id R C)
          fun _ _ => Commute.all _ _).comp (HQ.comul I hI)
      = (Algebra.ofId R C).comp (HQ.counit I hI) := by
  refine HQ.algHom_ext I hI ?_
  rw [AlgHom.comp_assoc, HQ.comul_comp_mk, ← AlgHom.comp_assoc,
    HQ.lift_map_mk_naturality_rTensor, AlgHom.comp_assoc,
    lift_antipode_id_comp_comulAlgHom, ← AlgHom.comp_assoc,
    show (π).comp (Algebra.ofId R A) = Algebra.ofId R C from
      AlgHom.ext fun _ => (π).commutes _,
    AlgHom.comp_assoc, HQ.counit_comp_mk]

theorem HQ.mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (AlgHom.id R C) (HQ.antipode I hI)
          fun _ _ => Commute.all _ _).comp (HQ.comul I hI)
      = (Algebra.ofId R C).comp (HQ.counit I hI) := by
  refine HQ.algHom_ext I hI ?_
  rw [AlgHom.comp_assoc, HQ.comul_comp_mk, ← AlgHom.comp_assoc,
    HQ.lift_map_mk_naturality_lTensor, AlgHom.comp_assoc,
    lift_id_antipode_comp_comulAlgHom, ← AlgHom.comp_assoc,
    show (π).comp (Algebra.ofId R A) = Algebra.ofId R C from
      AlgHom.ext fun _ => (π).commutes _,
    AlgHom.comp_assoc, HQ.counit_comp_mk]

scoped instance HQ.instHopfAlgebra : HopfAlgebra R C :=
  HopfAlgebra.ofAlgHom (HQ.antipode I hI)
    (HQ.mul_antipode_rTensor_comul I hI) (HQ.mul_antipode_lTensor_comul I hI)

p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ"

def HQ.mkB : A →ₐc[R] C :=
  BialgHom.ofAlgHom (HQ.mkₐ I hI) (HQ.counit_comp_mk I hI) (HQ.comul_comp_mk I hI).symm

@[scoped simp] theorem HQ.mkB_apply (x : A) : HQ.mkB I hI x = π x := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ"
theorem HQ.mkB_toAlgHom : (HQ.mkB I hI : A →ₐ[R] C) = π := rfl

scoped instance HQ.instModuleFinite [Module.Finite R A] : Module.Finite R C :=
  Module.Finite.of_surjective (π).toLinearMap (HQ.mkₐ_surjective I hI)

p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ"

theorem HQ.isCocomm [Coalgebra.IsCocomm R A] : Coalgebra.IsCocomm R C := by
  refine ⟨LinearMap.ext fun y => ?_⟩
  obtain ⟨x, rfl⟩ := HQ.mkₐ_surjective I hI y
  change (TensorProduct.comm R C C) (HQ.comul I hI (π x)) = HQ.comul I hI (π x)
  rw [HQ.comul_mk]
  have hnat : ∀ z : A ⊗[R] A, (TensorProduct.comm R C C)
      (TensorProduct.map (π).toLinearMap (π).toLinearMap z) =
      TensorProduct.map (π).toLinearMap (π).toLinearMap (TensorProduct.comm R A A z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add u v hu hv => simp [hu, hv]
  rw [hnat, Coalgebra.comm_comul]

end HopfQuot
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ"

section Include

variable {R : Type*} [CommRing R] {A B : Type*} [CommRing A] [CommRing B]
  [Bialgebra R A] [Bialgebra R B]

variable (R A B) in

def inclLeftB : A →ₐc[R] A ⊗[R] B :=
  BialgHom.ofAlgHom (Algebra.TensorProduct.includeLeft (S := R))
    (by
      ext a
      simp [Algebra.TensorProduct.includeLeft_apply])
    (by
      ext a
      simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply,
        Algebra.TensorProduct.includeLeft_apply]
      rw [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
      obtain ℛ := Coalgebra.Repr.arbitrary R a
      conv_lhs => rw [← ℛ.eq]
      conv_rhs => rw [← ℛ.eq]
      simp [TensorProduct.sum_tmul, map_sum, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul])

@[scoped simp] theorem inclLeftB_apply (a : A) : inclLeftB R A B a = a ⊗ₜ[R] (1 : B) := rfl

variable (R A B) in

def inclRightB : B →ₐc[R] A ⊗[R] B :=
  BialgHom.ofAlgHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B))
    (by
      ext b
      simp [Algebra.TensorProduct.includeRight_apply])
    (by
      ext b
      simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply,
        Algebra.TensorProduct.includeRight_apply]
      rw [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
      obtain ℛ := Coalgebra.Repr.arbitrary R b
      conv_lhs => rw [← ℛ.eq]
      conv_rhs => rw [← ℛ.eq]
      simp [TensorProduct.tmul_sum, map_sum, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul])

@[scoped simp] theorem inclRightB_apply (b : B) : inclRightB R A B b = (1 : A) ⊗ₜ[R] b := rfl

end Include
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ"

section TensorInj

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {P : Type*} [AddCommGroup P] [Module R P] [Module.Free R P]

theorem injective_of_basis_linearIndependent {S : Type*} [CommRing S] {M N : Type*}
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N] {ι : Type*}
    (b : Module.Basis ι S M) (g : M →ₗ[S] N) (h : LinearIndependent S (fun i => g (b i))) :
    Function.Injective g := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hx' : Finsupp.linearCombination S (fun i => g (b i)) (b.repr x) = 0 := by
    have := congrArg g (b.linearCombination_repr x)
    rw [hx] at this
    rw [← this, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
    simp
  have hrepr : b.repr x = 0 := by
    have h0 : Finsupp.linearCombination S (fun i => g (b i)) 0 = 0 := map_zero _
    exact h (hx'.trans h0.symm)
  simpa using congrArg b.repr.symm hrepr

theorem tensor_injective (f : P →ₗ[R] V) (hf : Function.Injective f)
    (θ : P ⊗[R] P →ₗ[R] V ⊗[K] V) (hθ : ∀ p p', θ (p ⊗ₜ p') = f p ⊗ₜ[K] f p') :
    Function.Injective θ := by
  let b := Module.Free.chooseBasis R P
  have hli : LinearIndependent R (fun i => f (b i)) :=
    (b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf))
  have hliK : LinearIndependent K (fun i => f (b i)) :=
    (LinearIndependent.iff_fractionRing R K).mp hli
  have hliKK := hliK.tmul_of_isDomain hliK
  have hliR : LinearIndependent R (fun i : _ × _ => f (b i.1) ⊗ₜ[K] f (b i.2)) :=
    (LinearIndependent.iff_fractionRing R K).mpr hliKK
  refine injective_of_basis_linearIndependent (b.tensorProduct b) θ ?_
  convert hliR with i
  rw [Module.Basis.tensorProduct_apply', hθ]
  rfl

theorem liftBaseChange_injective (f : P →ₗ[R] V) (hf : Function.Injective f) :
    Function.Injective (f.liftBaseChange K) := by
  let b := Module.Free.chooseBasis R P
  have hli : LinearIndependent R (fun i => f (b i)) :=
    (b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf))
  have hliK : LinearIndependent K (fun i => f (b i)) :=
    (LinearIndependent.iff_fractionRing R K).mp hli
  refine injective_of_basis_linearIndependent (Algebra.TensorProduct.basis K b)
    (f.liftBaseChange K) ?_
  convert hliK with i
  rw [Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end TensorInj
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ"

section BaseChangeFormulas

variable {R : Type*} [CommRing R] (K : Type*) [CommRing K] [Algebra R K]
  {H : Type*} [CommRing H] [HopfAlgebra R H]

theorem comul_one_tmul (h : H) {ιℛ : Type*} (ℛ : Coalgebra.Repr R h ιℛ) :
    Coalgebra.comul (R := K) ((1 : K) ⊗ₜ[R] h) =
      ∑ i ∈ ℛ.index, ((1 : K) ⊗ₜ[R] ℛ.left i) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] ℛ.right i) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← ℛ.eq]
  simp [TensorProduct.tmul_sum, map_sum, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]

theorem counit_one_tmul (h : H) :
    Coalgebra.counit (R := K) ((1 : K) ⊗ₜ[R] h) = algebraMap R K (Coalgebra.counit h) := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def, mul_one]

theorem antipode_one_tmul (h : H) :
    HopfAlgebra.antipode K ((1 : K) ⊗ₜ[R] h) = (1 : K) ⊗ₜ[R] HopfAlgebra.antipode R h := by
  rw [TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
    CommSemiring.antipode_eq_id, LinearMap.id_apply]

end BaseChangeFormulas
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ"

section FreeOfEmbedding

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

theorem free_of_injective (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    {X : Type*} [AddCommGroup X] [Module R X] [Module.Finite R X]
    (f : X →ₗ[R] V) (hf : Function.Injective f) : Module.Free R X := by
  haveI : Module.IsTorsionFree R X := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x hrx => ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    refine Or.inr (hf ?_)
    rw [map_zero]
    have h1 : r • f x = 0 := by rw [← map_smul, hrx, map_zero]
    rw [← algebraMap_smul K r, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd (IsFractionRing.injective R K (by rw [h1, map_zero])) hr
    · exact h1
  exact Module.free_of_finite_type_torsion_free'

end FreeOfEmbedding
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ"

section Main

set_option linter.unusedSectionVars false

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {H₀ : Type v} [CommRing H₀] [HopfAlgebra R H₀] [Module.Finite R H₀] [Module.Flat R H₀]
  [Coalgebra.IsCocomm R H₀]
  {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
  [Coalgebra.IsCocomm R H]
  (lam : (K ⊗[R] H₀) ≃ₐ[K] (K ⊗[R] H))

def incK₀ : H₀ →ₐ[R] K ⊗[R] H :=
  (lam.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

@[scoped simp] theorem incK₀_apply (y : H₀) : incK₀ K lam y = lam ((1 : K) ⊗ₜ[R] y) := rfl

def mulMap : H₀ ⊗[R] H →ₐ[R] K ⊗[R] H :=
  Algebra.TensorProduct.productMap (incK₀ K lam) Algebra.TensorProduct.includeRight

theorem mulMap_tmul (y : H₀) (h : H) :
    mulMap K lam (y ⊗ₜ[R] h) = lam ((1 : K) ⊗ₜ[R] y) * ((1 : K) ⊗ₜ[R] h) := rfl

theorem mulMap_tmul_one (y : H₀) : mulMap K lam (y ⊗ₜ[R] 1) = lam ((1 : K) ⊗ₜ[R] y) := by
  rw [mulMap, Algebra.TensorProduct.productMap_left_apply, incK₀_apply]

theorem mulMap_one_tmul (h : H) : mulMap K lam (1 ⊗ₜ[R] h) = (1 : K) ⊗ₜ[R] h := by
  rw [mulMap, Algebra.TensorProduct.productMap_right_apply,
    Algebra.TensorProduct.includeRight_apply]

def kerI : Ideal (H₀ ⊗[R] H) := RingHom.ker (mulMap K lam)

theorem mem_kerI (x : H₀ ⊗[R] H) : x ∈ kerI K lam ↔ mulMap K lam x = 0 := RingHom.mem_ker

local notation "G" => H₀ ⊗[R] H
local notation "E" => K ⊗[R] H
local notation "Q" => QS (kerI K lam)
local notation "πQ" => QS.mk R (kerI K lam)

def muQ : Q →ₐ[R] E :=
  QS.lift R (kerI K lam) (mulMap K lam) fun a ha => (mem_kerI K lam a).mp ha

@[scoped simp] theorem muQ_mk (x : G) : muQ K lam (πQ x) = mulMap K lam x := rfl

theorem muQ_injective : Function.Injective (muQ K lam) :=
  QS.lift_injective (kerI K lam) (mulMap K lam) (mem_kerI K lam)

scoped instance : Module.Finite R Q := QS.moduleFinite R (kerI K lam)

scoped instance : Module.Free R Q :=
  free_of_injective K (muQ K lam).toLinearMap (muQ_injective K lam)

def thetaL : Q →ₐ[R] E ⊗[K] E :=
  (Algebra.TensorProduct.includeLeft (R := K) (S := R) (A := E) (B := E)).comp (muQ K lam)

def thetaR : Q →ₐ[R] E ⊗[K] E :=
  ((Algebra.TensorProduct.includeRight (R := K) (A := E) (B := E)).restrictScalars R).comp
    (muQ K lam)

def theta : Q ⊗[R] Q →ₐ[R] E ⊗[K] E :=
  Algebra.TensorProduct.lift (thetaL K lam) (thetaR K lam)
    (fun p q => Commute.all (thetaL K lam p) (thetaR K lam q))

theorem theta_tmul (p q : Q) : theta K lam (p ⊗ₜ[R] q) = muQ K lam p ⊗ₜ[K] muQ K lam q := by
  rw [theta, Algebra.TensorProduct.lift_tmul]
  simp [thetaL, thetaR, Algebra.TensorProduct.tmul_mul_tmul]

theorem theta_injective : Function.Injective (theta K lam) :=
  tensor_injective (K := K) (muQ K lam).toLinearMap (muQ_injective K lam) (theta K lam).toLinearMap
    (fun p q => theta_tmul K lam p q)

variable
  (hlam_comul : ∀ x, Coalgebra.comul (R := K) (lam x) =
    (TensorProduct.map lam.toLinearMap lam.toLinearMap) (Coalgebra.comul (R := K) x))
  (hlam_counit : ∀ x, Coalgebra.counit (R := K) (lam x) = Coalgebra.counit (R := K) x)

include hlam_comul hlam_counit in

def lamB : (K ⊗[R] H₀) →ₐc[K] (K ⊗[R] H) :=
  BialgHom.ofAlgHom lam.toAlgHom
    (AlgHom.ext fun x => hlam_counit x)
    (AlgHom.ext fun x => (hlam_comul x).symm)

@[scoped simp] theorem lamB_apply (x : K ⊗[R] H₀) : lamB K lam hlam_comul hlam_counit x = lam x := rfl

include hlam_comul hlam_counit in

theorem lam_antipode (x : K ⊗[R] H₀) :
    lam (HopfAlgebra.antipode K x) = HopfAlgebra.antipode K (lam x) := by
  have h := bialgHom_comp_antipodeAlgHom (lamB K lam hlam_comul hlam_counit)
  have := DFunLike.congr_fun h x
  simpa using this

include hlam_counit in

theorem counit_mulMap :
    (Algebra.ofId R K).comp (Bialgebra.counitAlgHom R G) =
      ((Bialgebra.counitAlgHom K E).restrictScalars R).comp (mulMap K lam) := by
  apply Algebra.TensorProduct.ext
  · ext y
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Bialgebra.counitAlgHom_apply, AlgHom.coe_restrictScalars', mulMap_tmul_one]
    rw [TensorProduct.counit_tmul, Bialgebra.counit_one, one_smul, hlam_counit,
      counit_one_tmul, Algebra.ofId_apply]
  · ext h
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
      Bialgebra.counitAlgHom_apply, AlgHom.coe_restrictScalars', mulMap_one_tmul]
    rw [TensorProduct.counit_tmul, Bialgebra.counit_one, counit_one_tmul, Algebra.ofId_apply,
      smul_eq_mul, mul_one]

include hlam_comul hlam_counit in

theorem antipode_mulMap :
    (mulMap K lam).comp (antipodeAlgHom R G) =
      ((antipodeAlgHom K E).restrictScalars R).comp (mulMap K lam) := by
  apply Algebra.TensorProduct.ext
  · ext y
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      AlgHom.coe_restrictScalars', antipodeAlgHom_apply, mulMap_tmul_one]
    rw [TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
      HopfAlgebra.antipode_one, mulMap_tmul_one, ← lam_antipode K lam hlam_comul hlam_counit,
      antipode_one_tmul]
  · ext h
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
      AlgHom.coe_restrictScalars', antipodeAlgHom_apply, mulMap_one_tmul]
    rw [TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
      HopfAlgebra.antipode_one, mulMap_one_tmul, antipode_one_tmul]

include hlam_comul in

theorem theta_comul_mulMap :
    (theta K lam).comp ((Algebra.TensorProduct.map πQ πQ).comp (Bialgebra.comulAlgHom R G)) =
      ((Bialgebra.comulAlgHom K E).restrictScalars R).comp (mulMap K lam) := by
  apply Algebra.TensorProduct.ext
  · ext y
    obtain ℛ := Coalgebra.Repr.arbitrary R y
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      AlgHom.coe_restrictScalars', Bialgebra.comulAlgHom_apply, mulMap_tmul_one]
    rw [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def, ← ℛ.eq,
      hlam_comul, comul_one_tmul K y ℛ]
    simp [TensorProduct.sum_tmul, map_sum, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      theta_tmul, mulMap_tmul_one]
  · ext h
    obtain ℛ := Coalgebra.Repr.arbitrary R h
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
      AlgHom.coe_restrictScalars', Bialgebra.comulAlgHom_apply, mulMap_one_tmul]
    rw [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def, ← ℛ.eq,
      comul_one_tmul K h ℛ]
    simp [TensorProduct.tmul_sum, map_sum, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      theta_tmul, mulMap_one_tmul]

include hlam_comul hlam_counit in

theorem isHopfIdeal_kerI : IsHopfIdeal' R (kerI K lam) where
  counit_eq_zero x hx := by
    apply IsFractionRing.injective R K
    have := DFunLike.congr_fun (counit_mulMap K lam hlam_counit) x
    simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.counitAlgHom_apply,
      AlgHom.coe_restrictScalars', Algebra.ofId_apply] at this
    rw [this, (mem_kerI K lam x).mp hx, map_zero, map_zero]
  map_comul_eq_zero x hx := by
    apply theta_injective K lam
    have := DFunLike.congr_fun (theta_comul_mulMap K lam hlam_comul) x
    simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply,
      AlgHom.coe_restrictScalars'] at this
    rw [map_zero, this, (mem_kerI K lam x).mp hx, map_zero]
  antipode_mem x hx := by
    rw [mem_kerI]
    have := DFunLike.congr_fun (antipode_mulMap K lam hlam_comul hlam_counit) x
    simp only [AlgHom.coe_comp, Function.comp_apply, antipodeAlgHom_apply,
      AlgHom.coe_restrictScalars'] at this
    rw [this, (mem_kerI K lam x).mp hx, map_zero]

include hlam_comul hlam_counit in

theorem hI : IsHopfIdeal' R (kerI K lam) := isHopfIdeal_kerI K lam hlam_comul hlam_counit

local notation "CC" => HQ (kerI K lam) (hI K lam hlam_comul hlam_counit)
local notation "πC" => HQ.mkₐ (kerI K lam) (hI K lam hlam_comul hlam_counit)

def jZero : H₀ →ₐc[R] CC :=
  (HQ.mkB (kerI K lam) (hI K lam hlam_comul hlam_counit)).comp (inclLeftB R H₀ H)

def jOne : H →ₐc[R] CC :=
  (HQ.mkB (kerI K lam) (hI K lam hlam_comul hlam_counit)).comp (inclRightB R H₀ H)

theorem jZero_apply (y : H₀) : jZero K lam hlam_comul hlam_counit y = πC (y ⊗ₜ[R] 1) := rfl

theorem jOne_apply (h : H) : jOne K lam hlam_comul hlam_counit h = πC (1 ⊗ₜ[R] h) := rfl

def muC : CC →ₐ[R] E :=
  HQ.liftₐ (kerI K lam) (hI K lam hlam_comul hlam_counit) (mulMap K lam)
    fun a ha => (mem_kerI K lam a).mp ha

@[scoped simp] theorem muC_mk (x : G) : muC K lam hlam_comul hlam_counit (πC x) = mulMap K lam x := rfl

theorem muC_injective : Function.Injective (muC K lam hlam_comul hlam_counit) :=
  HQ.liftₐ_injective (kerI K lam) (hI K lam hlam_comul hlam_counit) (mulMap K lam) (mem_kerI K lam)

theorem freeC : Module.Free R CC :=
  free_of_injective K (muC K lam hlam_comul hlam_counit).toLinearMap
    (muC_injective K lam hlam_comul hlam_counit)

theorem flatC : Module.Flat R CC := by
  haveI := freeC K lam hlam_comul hlam_counit
  exact Module.Flat.of_free

theorem isCocommC : Coalgebra.IsCocomm R CC := HQ.isCocomm _ _

def nu : K ⊗[R] CC →ₗ[K] E := (muC K lam hlam_comul hlam_counit).toLinearMap.liftBaseChange K

theorem nu_tmul (k : K) (c : CC) :
    nu K lam hlam_comul hlam_counit (k ⊗ₜ[R] c) = k • muC K lam hlam_comul hlam_counit c :=
  LinearMap.liftBaseChange_tmul _ _ _ _

theorem nu_injective : Function.Injective (nu K lam hlam_comul hlam_counit) := by
  haveI := freeC K lam hlam_comul hlam_counit
  exact liftBaseChange_injective (K := K) _ (muC_injective K lam hlam_comul hlam_counit)

theorem nu_baseChange_jOne (v : K ⊗[R] H) :
    nu K lam hlam_comul hlam_counit
      (((jOne K lam hlam_comul hlam_counit : H →ₐc[R] CC) : H →ₐ[R] CC).toLinearMap.baseChange K v)
        = v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul k h =>
    rw [LinearMap.baseChange_tmul, nu_tmul]
    change k • muC K lam hlam_comul hlam_counit (πC (1 ⊗ₜ[R] h)) = k ⊗ₜ[R] h
    rw [muC_mk, mulMap_one_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add v w hv hw => rw [map_add, map_add, hv, hw]

theorem nu_baseChange_jZero (v : K ⊗[R] H₀) :
    nu K lam hlam_comul hlam_counit
      (((jZero K lam hlam_comul hlam_counit : H₀ →ₐc[R] CC) : H₀ →ₐ[R] CC).toLinearMap.baseChange K
        v) = lam v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul k y =>
    rw [LinearMap.baseChange_tmul, nu_tmul]
    change k • muC K lam hlam_comul hlam_counit (πC (y ⊗ₜ[R] 1)) = lam (k ⊗ₜ[R] y)
    rw [muC_mk, mulMap_tmul_one, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add v w hv hw => rw [map_add, map_add, hv, hw, map_add]

theorem jOne_injective : Function.Injective (jOne K lam hlam_comul hlam_counit) := by
  intro h h' hh
  rw [← sub_eq_zero, ← map_sub] at hh
  rw [← sub_eq_zero]
  set d := h - h'
  rw [jOne_apply] at hh
  have h1 : (1 : H₀) ⊗ₜ[R] d ∈ kerI K lam :=
    (HQ.mkₐ_eq_zero_iff _ _ _).mp hh
  rw [mem_kerI, mulMap_one_tmul] at h1
  exact Algebra.TensorProduct.includeRight_injective (R := R) (A := K) (B := H)
    (IsFractionRing.injective R K) (by rw [Algebra.TensorProduct.includeRight_apply, h1, map_zero])

theorem jZero_injective : Function.Injective (jZero K lam hlam_comul hlam_counit) := by
  intro y y' hy
  rw [← sub_eq_zero, ← map_sub] at hy
  rw [← sub_eq_zero]
  set d := y - y'
  rw [jZero_apply] at hy
  have h1 : d ⊗ₜ[R] (1 : H) ∈ kerI K lam :=
    (HQ.mkₐ_eq_zero_iff _ _ _).mp hy
  rw [mem_kerI, mulMap_tmul_one, map_eq_zero_iff _ lam.injective] at h1
  exact Algebra.TensorProduct.includeRight_injective (R := R) (A := K) (B := H₀)
    (IsFractionRing.injective R K) (by rw [Algebra.TensorProduct.includeRight_apply, h1, map_zero])

theorem baseChange_jOne_surjective :
    Function.Surjective
      (((jOne K lam hlam_comul hlam_counit : H →ₐc[R] CC) : H →ₐ[R] CC).toLinearMap.baseChange K) := by
  intro w
  refine ⟨nu K lam hlam_comul hlam_counit w, nu_injective K lam hlam_comul hlam_counit ?_⟩
  rw [nu_baseChange_jOne]

theorem baseChange_jZero_surjective :
    Function.Surjective
      (((jZero K lam hlam_comul hlam_counit : H₀ →ₐc[R] CC) : H₀ →ₐ[R] CC).toLinearMap.baseChange
        K) := by
  intro w
  refine ⟨lam.symm (nu K lam hlam_comul hlam_counit w), nu_injective K lam hlam_comul hlam_counit ?_⟩
  rw [nu_baseChange_jZero, AlgEquiv.apply_symm_apply]

theorem compat (y : H₀) :
    (1 : K) ⊗ₜ[R] (jZero K lam hlam_comul hlam_counit y) =
      (((jOne K lam hlam_comul hlam_counit : H →ₐc[R] CC) : H →ₐ[R] CC).toLinearMap.baseChange K)
        (lam ((1 : K) ⊗ₜ[R] y)) := by
  apply nu_injective K lam hlam_comul hlam_counit
  rw [nu_baseChange_jOne, nu_tmul, one_smul]
  change muC K lam hlam_comul hlam_counit (πC (y ⊗ₜ[R] 1)) = _
  rw [muC_mk, mulMap_tmul_one]

include hlam_comul hlam_counit in
theorem main :
    ∃ (C : Type v) (_ : CommRing C) (_ : HopfAlgebra R C) (_ : Module.Finite R C)
      (_ : Module.Flat R C) (_ : Coalgebra.IsCocomm R C)
      (j₀ : H₀ →ₐc[R] C) (j : H →ₐc[R] C),
      Function.Injective j₀ ∧ Function.Injective j ∧
      Function.Surjective ((j₀ : H₀ →ₐ[R] C).toLinearMap.baseChange K) ∧
      Function.Surjective ((j : H →ₐ[R] C).toLinearMap.baseChange K) ∧
      ∀ y : H₀, (1 : K) ⊗ₜ[R] (j₀ y) =
        ((j : H →ₐ[R] C).toLinearMap.baseChange K) (lam ((1 : K) ⊗ₜ[R] y)) :=
  ⟨CC, inferInstance, inferInstance, inferInstance, flatC K lam hlam_comul hlam_counit,
    isCocommC K lam hlam_comul hlam_counit,
    jZero K lam hlam_comul hlam_counit, jOne K lam hlam_comul hlam_counit,
    jZero_injective K lam hlam_comul hlam_counit, jOne_injective K lam hlam_comul hlam_counit,
    baseChange_jZero_surjective K lam hlam_comul hlam_counit,
    baseChange_jOne_surjective K lam hlam_comul hlam_counit,
    compat K lam hlam_comul hlam_counit⟩

end Main
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ"

end SupModelProof
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof"

end
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.QS P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.HQ P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof"

open scoped TensorProduct in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {H₀ : Type v} [CommRing H₀] [HopfAlgebra R H₀] [Module.Finite R H₀] [Module.Flat R H₀]
    [Coalgebra.IsCocomm R H₀]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    (lam : (K ⊗[R] H₀) ≃ₐ[K] (K ⊗[R] H))
    (hlam_comul : ∀ x, Coalgebra.comul (R := K) (lam x) =
      (TensorProduct.map lam.toLinearMap lam.toLinearMap) (Coalgebra.comul (R := K) x))
    (hlam_counit : ∀ x, Coalgebra.counit (R := K) (lam x) = Coalgebra.counit (R := K) x) :
    ∃ (C : Type v) (_ : CommRing C) (_ : HopfAlgebra R C) (_ : Module.Finite R C)
      (_ : Module.Flat R C) (_ : Coalgebra.IsCocomm R C)
      (j₀ : H₀ →ₐc[R] C) (j : H →ₐc[R] C),
      Function.Injective j₀ ∧ Function.Injective j ∧
      Function.Surjective ((j₀ : H₀ →ₐ[R] C).toLinearMap.baseChange K) ∧
      Function.Surjective ((j : H →ₐ[R] C).toLinearMap.baseChange K) ∧
      ∀ y : H₀, (1 : K) ⊗ₜ[R] (j₀ y) =
        ((j : H →ₐ[R] C).toLinearMap.baseChange K) (lam ((1 : K) ⊗ₜ[R] y)) :=
  SupModelProof.main K lam hlam_comul hlam_counit

end S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange
end P2MW
export P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange (solution)

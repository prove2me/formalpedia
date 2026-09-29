-- Prove2me | solution 1 for HopfAlgebra.exists_finite_free_quotient_bialgHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8d5d0a08-280a-58d4-be02-47a5e0a20a3e

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finite_free_quotient_bialgHom

namespace A3F

open scoped TensorProduct

section Carrier

variable (R : Type*) (A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

def torsIdeal : Ideal A where
  carrier := {a | ∃ r : R, r ≠ 0 ∧ r • a = 0}
  zero_mem' := ⟨1, one_ne_zero, smul_zero _⟩
  add_mem' := by
    rintro a b ⟨r, hr, hra⟩ ⟨s, hs, hsb⟩
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    have ha : (r * s) • a = 0 := by rw [mul_comm, mul_smul, hra, smul_zero]
    have hb : (r * s) • b = 0 := by rw [mul_smul, hsb, smul_zero]
    rw [smul_add, ha, hb, add_zero]
  smul_mem' := by
    rintro c a ⟨r, hr, hra⟩
    exact ⟨r, hr, by rw [smul_eq_mul, ← mul_smul_comm, hra, mul_zero]⟩

lemma mem_torsIdeal_iff {a : A} : a ∈ torsIdeal R A ↔ ∃ r : R, r ≠ 0 ∧ r • a = 0 := Iff.rfl

scoped instance : Module.IsTorsionFree R (A ⧸ torsIdeal R A) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r x hx => ?_
  by_cases hr : r = 0
  · exact Or.inl hr
  refine Or.inr ?_
  induction x using Quotient.inductionOn' with
  | h a =>
    change (Ideal.Quotient.mk (torsIdeal R A)) (r • a) = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_torsIdeal_iff] at hx
    obtain ⟨s, hs, hsa⟩ := hx
    change (Ideal.Quotient.mk (torsIdeal R A)) a = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_torsIdeal_iff]
    exact ⟨s * r, mul_ne_zero hs hr, by rw [mul_smul]; exact hsa⟩

scoped instance [Module.Finite R A] : Module.Finite R (A ⧸ torsIdeal R A) :=
  Module.Finite.of_surjective (IsScalarTower.toAlgHom R A (A ⧸ torsIdeal R A)).toLinearMap
    Ideal.Quotient.mk_surjective

lemma apply_eq_zero_of_mem_torsIdeal {L : Type*} [AddCommGroup L] [Module R L]
    [Module.IsTorsionFree R L] {F : Type*} [FunLike F A L] [LinearMapClass F R A L] (f : F)
    (a : A) (ha : a ∈ torsIdeal R A) : f a = 0 := by
  obtain ⟨r, hr, hra⟩ := ha
  have h : r • f a = 0 := by rw [← map_smul, hra, map_zero]
  exact (smul_eq_zero.mp h).resolve_left hr

lemma torsIdeal_le_ker {L : Type*} [CommRing L] [Algebra R L] [Module.IsTorsionFree R L]
    (f : A →ₐ[R] L) : ∀ a ∈ torsIdeal R A, f a = 0 :=
  fun a ha => apply_eq_zero_of_mem_torsIdeal R A f a ha

lemma bijective_comp_mk {L : Type*} [CommRing L] [Algebra R L] [Module.IsTorsionFree R L] :
    Function.Bijective
      (fun (f : (A ⧸ torsIdeal R A) →ₐ[R] L) ↦ f.comp (Ideal.Quotient.mkₐ R (torsIdeal R A))) := by
  constructor
  · intro f g hfg
    exact (AlgHom.cancel_right (by
      simpa using (Ideal.Quotient.mk_surjective (I := torsIdeal R A)))).mp hfg
  · intro f
    exact ⟨Ideal.Quotient.liftₐ _ f (torsIdeal_le_ker R A f), Ideal.Quotient.liftₐ_comp _ f _⟩

def mkL : A →ₗ[R] A ⧸ torsIdeal R A := (Ideal.Quotient.mkₐ R (torsIdeal R A)).toLinearMap

@[scoped simp] lemma mkL_apply (a : A) : mkL R A a = Ideal.Quotient.mk (torsIdeal R A) a := rfl

end Carrier

section Hopf

variable (R : Type*) (A : Type*) [CommRing R] [CommRing A] [HopfAlgebra R A]

noncomputable def antipodeAlgHom : A →ₐ[R] A :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul_antidistrib, mul_comm])

@[scoped simp] lemma antipodeAlgHom_apply (a : A) : antipodeAlgHom R A a = HopfAlgebra.antipode R a :=
  rfl

variable [IsDomain R]

noncomputable def counitQ : (A ⧸ torsIdeal R A) →ₐ[R] R :=
  Ideal.Quotient.liftₐ (torsIdeal R A) (Bialgebra.counitAlgHom R A)
    (fun a ha => apply_eq_zero_of_mem_torsIdeal R A _ a ha)

noncomputable def antipodeQ : (A ⧸ torsIdeal R A) →ₐ[R] (A ⧸ torsIdeal R A) :=
  Ideal.Quotient.liftₐ (torsIdeal R A)
    ((Ideal.Quotient.mkₐ R (torsIdeal R A)).comp (antipodeAlgHom R A))
    (fun a ha => apply_eq_zero_of_mem_torsIdeal R A _ a ha)

@[scoped simp] lemma antipodeQ_mk (a : A) :
    antipodeQ R A (Ideal.Quotient.mk (torsIdeal R A) a)
      = Ideal.Quotient.mk (torsIdeal R A) (HopfAlgebra.antipode R a) := rfl

lemma antipodeQ_comp_mkL :
    (antipodeQ R A).toLinearMap ∘ₗ mkL R A = mkL R A ∘ₗ HopfAlgebra.antipode R := rfl

lemma mul'_rTensor_antipode_map (z : A ⊗[R] A) :
    LinearMap.mul' R (A ⧸ torsIdeal R A)
        ((antipodeQ R A).toLinearMap.rTensor (A ⧸ torsIdeal R A)
          (TensorProduct.map (mkL R A) (mkL R A) z))
      = Ideal.Quotient.mk (torsIdeal R A)
          (LinearMap.mul' R A ((HopfAlgebra.antipode R).rTensor A z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply, mkL_apply,
      AlgHom.toLinearMap_apply, antipodeQ_mk, map_mul]

lemma mul'_lTensor_antipode_map (z : A ⊗[R] A) :
    LinearMap.mul' R (A ⧸ torsIdeal R A)
        ((antipodeQ R A).toLinearMap.lTensor (A ⧸ torsIdeal R A)
          (TensorProduct.map (mkL R A) (mkL R A) z))
      = Ideal.Quotient.mk (torsIdeal R A)
          (LinearMap.mul' R A ((HopfAlgebra.antipode R).lTensor A z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply, mkL_apply,
      AlgHom.toLinearMap_apply, antipodeQ_mk, map_mul]

variable [IsPrincipalIdealRing R] [Module.Finite R A]

noncomputable def comulQ : (A ⧸ torsIdeal R A) →ₐ[R] (A ⧸ torsIdeal R A) ⊗[R] (A ⧸ torsIdeal R A) :=
  Ideal.Quotient.liftₐ (torsIdeal R A)
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (torsIdeal R A))
      (Ideal.Quotient.mkₐ R (torsIdeal R A))).comp (Bialgebra.comulAlgHom R A))
    (fun a ha => apply_eq_zero_of_mem_torsIdeal R A _ a ha)

noncomputable scoped instance instCoalgebraStruct : CoalgebraStruct R (A ⧸ torsIdeal R A) where
  comul := (comulQ R A).toLinearMap
  counit := (counitQ R A).toLinearMap

@[scoped simp] lemma comul_mk (a : A) :
    Coalgebra.comul (R := R) (Ideal.Quotient.mk (torsIdeal R A) a)
      = TensorProduct.map (mkL R A) (mkL R A) (Coalgebra.comul (R := R) a) := rfl

@[scoped simp] lemma counit_mk (a : A) :
    Coalgebra.counit (R := R) (Ideal.Quotient.mk (torsIdeal R A) a) = Coalgebra.counit (R := R) a :=
  rfl

lemma comul_comp_mkL :
    Coalgebra.comul (R := R) (A := A ⧸ torsIdeal R A) ∘ₗ mkL R A
      = TensorProduct.map (mkL R A) (mkL R A) ∘ₗ Coalgebra.comul := rfl

lemma counit_comp_mkL :
    Coalgebra.counit (R := R) (A := A ⧸ torsIdeal R A) ∘ₗ mkL R A = Coalgebra.counit := rfl

noncomputable scoped instance instCoalgebra : Coalgebra R (A ⧸ torsIdeal R A) where
  coassoc := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have key := congr(TensorProduct.map (mkL R A) (TensorProduct.map (mkL R A) (mkL R A))
      $(Coalgebra.coassoc_apply (R := R) a))
    rw [TensorProduct.map_map_assoc, LinearMap.map_rTensor, LinearMap.map_lTensor] at key
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, comul_mk, LinearMap.rTensor_map,
      LinearMap.lTensor_map, comul_comp_mkL] using key
  rTensor_counit_comp_comul := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have key : TensorProduct.map (Coalgebra.counit (R := R) (A := A)) (mkL R A) (Coalgebra.comul a)
        = (1 : R) ⊗ₜ[R] Ideal.Quotient.mk (torsIdeal R A) a := by
      rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul,
        LinearMap.lTensor_tmul, mkL_apply]
    simpa only [LinearMap.comp_apply, comul_mk, LinearMap.rTensor_map, counit_comp_mkL,
      TensorProduct.mk_apply] using key
  lTensor_counit_comp_comul := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have key : TensorProduct.map (mkL R A) (Coalgebra.counit (R := R) (A := A)) (Coalgebra.comul a)
        = Ideal.Quotient.mk (torsIdeal R A) a ⊗ₜ[R] (1 : R) := by
      rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul,
        LinearMap.rTensor_tmul, mkL_apply]
    simpa only [LinearMap.comp_apply, comul_mk, LinearMap.lTensor_map, counit_comp_mkL,
      TensorProduct.mk_apply, LinearMap.flip_apply] using key

noncomputable scoped instance instBialgebra : Bialgebra R (A ⧸ torsIdeal R A) :=
  Bialgebra.mk' R (A ⧸ torsIdeal R A)
    (map_one (counitQ R A)) (fun {a b} => map_mul (counitQ R A) a b)
    (map_one (comulQ R A)) (fun {a b} => map_mul (comulQ R A) a b)

noncomputable scoped instance instHopfAlgebra : HopfAlgebra R (A ⧸ torsIdeal R A) where
  antipode := (antipodeQ R A).toLinearMap
  mul_antipode_rTensor_comul := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have key := congr(Ideal.Quotient.mk (torsIdeal R A)
      $(HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) a))
    rw [Ideal.Quotient.mk_algebraMap] at key
    simpa only [LinearMap.comp_apply, comul_mk, mul'_rTensor_antipode_map, counit_mk,
      Algebra.linearMap_apply] using key
  mul_antipode_lTensor_comul := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have key := congr(Ideal.Quotient.mk (torsIdeal R A)
      $(HopfAlgebra.mul_antipode_lTensor_comul_apply (R := R) a))
    rw [Ideal.Quotient.mk_algebraMap] at key
    simpa only [LinearMap.comp_apply, comul_mk, mul'_lTensor_antipode_map, counit_mk,
      Algebra.linearMap_apply] using key

lemma isCocomm [Coalgebra.IsCocomm R A] : Coalgebra.IsCocomm R (A ⧸ torsIdeal R A) where
  comm_comp_comul := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have key := congr(TensorProduct.map (mkL R A) (mkL R A) $(Coalgebra.comm_comul R a))
    rw [TensorProduct.map_comm] at key
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, comul_mk] using key

noncomputable def mkBialgHom : A →ₐc[R] (A ⧸ torsIdeal R A) :=
  BialgHom.ofAlgHom (Ideal.Quotient.mkₐ R (torsIdeal R A))
    (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

lemma mkBialgHom_toAlgHom :
    (mkBialgHom R A : A →ₐ[R] A ⧸ torsIdeal R A) = Ideal.Quotient.mkₐ R (torsIdeal R A) := rfl

lemma mkBialgHom_surjective : Function.Surjective (mkBialgHom R A) := fun x => by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨a, rfl⟩

end Hopf

end A3F
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finite_free_quotient_bialgHom.A3F"

universe u v w

theorem solution
    (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing A] [HopfAlgebra R A] [Module.Finite R A] :
    ∃ (B : Type v) (_ : CommRing B) (_ : HopfAlgebra R B) (π : A →ₐc[R] B),
      Module.Finite R B ∧ Module.Free R B ∧ Module.Flat R B ∧
      (Coalgebra.IsCocomm R A → Coalgebra.IsCocomm R B) ∧
      Function.Surjective ⇑π ∧
      ∀ (L : Type w) [CommRing L] [Algebra R L] [Module.IsTorsionFree R L],
        Function.Bijective (fun f : B →ₐ[R] L => f.comp (π : A →ₐ[R] B)) :=
  ⟨A ⧸ A3F.torsIdeal R A, inferInstance, inferInstance, A3F.mkBialgHom R A,
    inferInstance, inferInstance, inferInstance,
    fun h => by haveI := h; exact A3F.isCocomm R A,
    A3F.mkBialgHom_surjective R A,
    fun L _ _ _ => A3F.bijective_comp_mk R A⟩

end S_HopfAlgebra_exists_finite_free_quotient_bialgHom
end P2MW
export P2MW.S_HopfAlgebra_exists_finite_free_quotient_bialgHom (solution)

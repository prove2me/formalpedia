-- Prove2me | solution 1 for HopfAlgebra.bijective_of_bijective_baseChange_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/57ddb485-2fe1-5943-a9eb-895271c7b46f

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_surjective_of_bijective_of_bijOn_hopfKer
import Theorems.Thm_HopfAlgebra_surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one
p2m_attr_erase "instance" "CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul"

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one ofAlgHom mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul mul_antipode_lTensor_comul mul_antipode_rTensor_comul_apply coaction coaction_apply hopfKer mem_hopfKer_iff HopfKerHopf.ι₂ HopfKerHopf.ι₂_injective HopfKerHopf.counit_coe HopfKerHopf.ι₂_comul surjective_of_bijective_of_bijOn_hopfKer surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple"
namespace RaynaudConservative
p2m_open "HopfAlgebra"

open Coalgebra Bialgebra WithConv

section AntipodeAlgHom

variable (R : Type*) [CommRing R] (H : Type*) [CommRing H] [HopfAlgebra R H]

noncomputable def antipodeAlgHom' : H →ₐ[R] H :=
  AlgHom.ofLinearMap (antipode R) antipode_one fun a b => by
    rw [antipode_mul, mul_comm]

@[scoped simp] theorem antipodeAlgHom'_apply (x : H) : antipodeAlgHom' R H x = antipode R x := rfl

variable {R H}
variable {A : Type*} [CommRing A] [Algebra R A]

theorem lift_comp_antipodeAlgHom'_apply (φ : H →ₐ[R] A) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift φ (φ.comp (antipodeAlgHom' R H)) (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R H ((antipode R).lTensor H z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem lift_antipodeAlgHom'_comp_apply (φ : H →ₐ[R] A) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift (φ.comp (antipodeAlgHom' R H)) φ (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R H ((antipode R).rTensor H z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

end AntipodeAlgHom

section IsHopfIdeal'

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

class IsHopfIdeal' (I : Ideal H) : Prop where
  map_mkₐ_comul_eq_zero : ∀ x ∈ I,
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) x) = 0
  counit_eq_zero : ∀ x ∈ I, Coalgebra.counit (R := R) x = 0
  antipode_mem : ∀ x ∈ I, HopfAlgebra.antipode R x ∈ I

end IsHopfIdeal'

namespace HopfIdealQuotient

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]
variable (I : Ideal H) [hI : IsHopfIdeal' R I]

private noncomputable def _root_.HopfAlgebra.RaynaudConservative.HopfIdealQuotient.comul : H ⧸ I →ₐ[R] (H ⧸ I) ⊗[R] (H ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (comulAlgHom R H))
    (fun x hx => hI.map_mkₐ_comul_eq_zero x hx)

p2m_export "HopfAlgebra.RaynaudConservative.HopfIdealQuotient" "comul"
theorem comul_comp_mkₐ :
    (comul R I).comp (Ideal.Quotient.mkₐ R I) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
        (comulAlgHom R H) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem comul_mk (x : H) :
    comul R I (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

private noncomputable def _root_.HopfAlgebra.RaynaudConservative.HopfIdealQuotient.counit : H ⧸ I →ₐ[R] R :=
  Ideal.Quotient.liftₐ I (counitAlgHom R H) (fun x hx => hI.counit_eq_zero x hx)

p2m_export "HopfAlgebra.RaynaudConservative.HopfIdealQuotient" "counit"
theorem counit_comp_mkₐ : (counit R I).comp (Ideal.Quotient.mkₐ R I) = counitAlgHom R H :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem counit_mk (x : H) :
    counit R I (Ideal.Quotient.mk I x) = Coalgebra.counit (R := R) x := rfl

private noncomputable def _root_.HopfAlgebra.RaynaudConservative.HopfIdealQuotient.antipode : H ⧸ I →ₐ[R] H ⧸ I :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R I).comp (antipodeAlgHom' R H)) (fun x hx => by
    simp only [AlgHom.comp_apply, antipodeAlgHom'_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hI.antipode_mem x hx)

p2m_export "HopfAlgebra.RaynaudConservative.HopfIdealQuotient" "antipode"
theorem antipode_comp_mkₐ :
    (antipode R I).comp (Ideal.Quotient.mkₐ R I) =
      (Ideal.Quotient.mkₐ R I).comp (antipodeAlgHom' R H) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem antipode_mk (x : H) :
    antipode R I (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (HopfAlgebra.antipode R x) := rfl

private theorem map_apply_eq_linearMap {A B C D : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] C) (g : B →ₐ[R] D) (z : A ⊗[R] B) :
    Algebra.TensorProduct.map f g z = TensorProduct.map f.toLinearMap g.toLinearMap z := rfl

private theorem _root_.HopfAlgebra.RaynaudConservative.HopfIdealQuotient.rTensor_counit_comul :
    (Algebra.TensorProduct.map (counit R I) (.id R (H ⧸ I))).comp (comul R I) =
      (Algebra.TensorProduct.lid R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.lid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (counitAlgHom R H).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.lTensor R) ∘ₗ
          ((counitAlgHom R H).toLinearMap.rTensor H) from
      (LinearMap.lTensor_comp_rTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom R H).toLinearMap.rTensor H) (Coalgebra.comul x) = 1 ⊗ₜ x from
    Coalgebra.rTensor_counit_comul x]
  simp

p2m_export "HopfAlgebra.RaynaudConservative.HopfIdealQuotient" "rTensor_counit_comul"
private theorem _root_.HopfAlgebra.RaynaudConservative.HopfIdealQuotient.lTensor_counit_comul :
    (Algebra.TensorProduct.map (.id R (H ⧸ I)) (counit R I)).comp (comul R I) =
      (Algebra.TensorProduct.rid R R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.rid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap (counitAlgHom R H).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.rTensor R) ∘ₗ
          ((counitAlgHom R H).toLinearMap.lTensor H) from
      (LinearMap.rTensor_comp_lTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom R H).toLinearMap.lTensor H) (Coalgebra.comul x) = x ⊗ₜ 1 from
    Coalgebra.lTensor_counit_comul x]
  simp

p2m_export "HopfAlgebra.RaynaudConservative.HopfIdealQuotient" "lTensor_counit_comul"
private theorem assoc_map_map_apply {A B : Type*} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) (z : (A ⊗[R] A) ⊗[R] A) :
    (Algebra.TensorProduct.assoc R R R B B B)
        (Algebra.TensorProduct.map (Algebra.TensorProduct.map f f) f z) =
      Algebra.TensorProduct.map f (Algebra.TensorProduct.map f f)
        (Algebra.TensorProduct.assoc R R R A A A z) := by
  induction z with
  | zero => simp
  | tmul xy c =>
    induction xy with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coassoc :
    (Algebra.TensorProduct.assoc R R R (H ⧸ I) (H ⧸ I) (H ⧸ I)).toAlgHom.comp
        ((Algebra.TensorProduct.map (comul R I) (.id R (H ⧸ I))).comp (comul R I)) =
      (Algebra.TensorProduct.map (.id R (H ⧸ I)) (comul R I)).comp (comul R I) := by
  refine Ideal.Quotient.algHom_ext R ?_
  refine AlgHom.ext fun x => ?_
  set π := Ideal.Quotient.mkₐ R I
  have hL : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.map (comul R I) (.id R (H ⧸ I)) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.map π π) π
          (Algebra.TensorProduct.map (comulAlgHom R H) (.id R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hR : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.map (.id R (H ⧸ I)) (comul R I) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map π (Algebra.TensorProduct.map π π)
          (Algebra.TensorProduct.map (.id R H) (comulAlgHom R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hx : comul R I (π x) = Algebra.TensorProduct.map π π (comulAlgHom R H x) := by
    simp [π, Ideal.Quotient.mkₐ_eq_mk]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, hx, hL, hR, assoc_map_map_apply]
  congr 1
  have hassoc : ∀ z : (H ⊗[R] H) ⊗[R] H,
      Algebra.TensorProduct.assoc R R R H H H z = TensorProduct.assoc R H H H z := by
    intro z
    induction z with
    | zero => simp
    | tmul xy c =>
      induction xy with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [map_apply_eq_linearMap, map_apply_eq_linearMap, hassoc]
  exact Coalgebra.coassoc_apply x

noncomputable scoped instance instBialgebra : Bialgebra R (H ⧸ I) :=
  Bialgebra.ofAlgHom (comul R I) (counit R I) (coassoc R I) (rTensor_counit_comul R I)
    (lTensor_counit_comul R I)

theorem comulAlgHom_eq : comulAlgHom R (H ⧸ I) = comul R I := rfl

theorem counitAlgHom_eq : counitAlgHom R (H ⧸ I) = counit R I := rfl

theorem coalgebra_comul_mk (x : H) :
    Coalgebra.comul (R := R) (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

theorem coalgebra_counit_mk (x : H) :
    Coalgebra.counit (R := R) (Ideal.Quotient.mk I x) = Coalgebra.counit (R := R) x := rfl

private theorem lift_antipode_id_comp_map :
    (Algebra.TensorProduct.lift (antipode R I) (.id R (H ⧸ I)) fun _ _ => .all _ _).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)) =
      (Ideal.Quotient.mkₐ R I).comp
        (Algebra.TensorProduct.lift (antipodeAlgHom' R H) (.id R H) fun _ _ => .all _ _) := by
  ext x
  · simp [Ideal.Quotient.mkₐ_eq_mk]
  · simp [Ideal.Quotient.mkₐ_eq_mk]

private theorem lift_id_antipode_comp_map :
    (Algebra.TensorProduct.lift (.id R (H ⧸ I)) (antipode R I) fun _ _ => .all _ _).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)) =
      (Ideal.Quotient.mkₐ R I).comp
        (Algebra.TensorProduct.lift (.id R H) (antipodeAlgHom' R H) fun _ _ => .all _ _) := by
  ext x
  · simp [Ideal.Quotient.mkₐ_eq_mk]
  · simp [Ideal.Quotient.mkₐ_eq_mk]

private theorem lift_antipodeAlgHom'_id_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (antipodeAlgHom' R H) (.id R H) fun _ _ => .all _ _).comp
        (comulAlgHom R H) = (Algebra.ofId R H).comp (counitAlgHom R H) := by
  refine AlgHom.ext fun x => ?_
  have h := lift_antipodeAlgHom'_comp_apply (AlgHom.id R H) (Coalgebra.comul (R := R) x)
  simp only [AlgHom.id_comp] at h
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, h, mul_antipode_rTensor_comul_apply]
  simp [Algebra.ofId_apply]

private theorem lift_id_antipodeAlgHom'_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (.id R H) (antipodeAlgHom' R H) fun _ _ => .all _ _).comp
        (comulAlgHom R H) = (Algebra.ofId R H).comp (counitAlgHom R H) := by
  refine AlgHom.ext fun x => ?_
  have h := lift_comp_antipodeAlgHom'_apply (AlgHom.id R H) (Coalgebra.comul (R := R) x)
  simp only [AlgHom.id_comp] at h
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, h, mul_antipode_lTensor_comul_apply]
  simp [Algebra.ofId_apply]

theorem mul_antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode R I) (.id R (H ⧸ I)) fun _ _ => .all _ _).comp
        (comulAlgHom R (H ⧸ I)) =
      (Algebra.ofId R (H ⧸ I)).comp (counitAlgHom R (H ⧸ I)) := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [comulAlgHom_eq, counitAlgHom_eq, AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc,
    lift_antipode_id_comp_map, AlgHom.comp_assoc, lift_antipodeAlgHom'_id_comp_comulAlgHom,
    AlgHom.comp_assoc, counit_comp_mkₐ, ← AlgHom.comp_assoc]
  congr 1

theorem mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (.id R (H ⧸ I)) (antipode R I) fun _ _ => .all _ _).comp
        (comulAlgHom R (H ⧸ I)) =
      (Algebra.ofId R (H ⧸ I)).comp (counitAlgHom R (H ⧸ I)) := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [comulAlgHom_eq, counitAlgHom_eq, AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc,
    lift_id_antipode_comp_map, AlgHom.comp_assoc, lift_id_antipodeAlgHom'_comp_comulAlgHom,
    AlgHom.comp_assoc, counit_comp_mkₐ, ← AlgHom.comp_assoc]
  congr 1

noncomputable scoped instance instHopfAlgebra : HopfAlgebra R (H ⧸ I) :=
  HopfAlgebra.ofAlgHom (antipode R I) (mul_antipode_rTensor_comul R I)
    (mul_antipode_lTensor_comul R I)

scoped instance instIsCocomm [Coalgebra.IsCocomm R H] : Coalgebra.IsCocomm R (H ⧸ I) where
  comm_comp_comul := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [LinearMap.comp_apply, coalgebra_comul_mk]
    conv_rhs => rw [← Coalgebra.comm_comp_comul R H]
    rw [LinearMap.comp_apply]
    generalize Coalgebra.comul (R := R) x = z
    induction z with
    | zero => simp
    | tmul a b => simp
    | add z w hz hw => simp only [map_add, hz, hw]

noncomputable def quotientBialgHom : H →ₐc[R] H ⧸ I :=
  BialgHom.ofAlgHom (Ideal.Quotient.mkₐ R I) (counit_comp_mkₐ R I) (comul_comp_mkₐ R I).symm

@[scoped simp] theorem quotientBialgHom_apply (x : H) :
    quotientBialgHom R I x = Ideal.Quotient.mk I x := rfl

theorem quotientBialgHom_toAlgHom :
    (quotientBialgHom R I : H →ₐ[R] H ⧸ I) = Ideal.Quotient.mkₐ R I := rfl

theorem quotientBialgHom_surjective : Function.Surjective (quotientBialgHom R I) :=
  Ideal.Quotient.mk_surjective

end HopfIdealQuotient
p2m_reactivate "P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one.HopfAlgebra.RaynaudConservative.HopfIdealQuotient"

section Convolution

variable {R : Type*} [CommRing R]
variable {H : Type*} [CommRing H] [HopfAlgebra R H]
variable {G : Type*} [CommRing G] [HopfAlgebra R G]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {B : Type*} [CommRing B] [Algebra R B]

noncomputable def convPrecomp (A : Type*) [CommRing A] [Algebra R A] (π : H →ₐc[R] G) :
    WithConv (G →ₐ[R] A) →* WithConv (H →ₐ[R] A) where
  toFun f := toConv (f.ofConv.comp (π : H →ₐ[R] G))
  map_one' := by
    refine WithConv.ext ?_
    simp only [ofConv_toConv, AlgHom.convOne_def, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  map_mul' f g := by
    rw [AlgHom.convMul_comp_bialgHom_distrib]

@[scoped simp] theorem convPrecomp_apply (π : H →ₐc[R] G) (f : WithConv (G →ₐ[R] A)) :
    convPrecomp A π f = toConv (f.ofConv.comp (π : H →ₐ[R] G)) := rfl

noncomputable def convPostcomp (H : Type*) [CommRing H] [HopfAlgebra R H] (h : A →ₐ[R] B) :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] B) where
  toFun f := toConv (h.comp f.ofConv)
  map_one' := by
    refine WithConv.ext ?_
    simp only [ofConv_toConv, AlgHom.convOne_def, ← AlgHom.comp_assoc]
    congr 1
    ext
  map_mul' f g := by
    rw [AlgHom.comp_convMul_distrib]

@[scoped simp] theorem convPostcomp_apply (h : A →ₐ[R] B) (f : WithConv (H →ₐ[R] A)) :
    convPostcomp H h f = toConv (h.comp f.ofConv) := rfl

theorem pow_eq_one_of_surjective (π : H →ₐc[R] G) (hπ : Function.Surjective π) (m : ℕ)
    (hH : ∀ f : WithConv (H →ₐ[R] A), f ^ m = 1) (f : WithConv (G →ₐ[R] A)) : f ^ m = 1 := by
  have h1 : convPrecomp A π (f ^ m) = convPrecomp A π 1 := by
    rw [map_pow, map_one]
    exact hH _
  simp only [convPrecomp_apply] at h1
  have h2 : (f ^ m).ofConv.comp (π : H →ₐ[R] G) = (1 : WithConv (G →ₐ[R] A)).ofConv.comp
      (π : H →ₐ[R] G) := congrArg WithConv.ofConv h1
  apply WithConv.ofConv_injective
  exact AlgHom.ext fun y => by
    obtain ⟨x, rfl⟩ := hπ y
    exact congrArg (fun g : H →ₐ[R] A => g x) h2

theorem toConv_id_pow_eq_one_of_injective (ι : G →ₐc[R] H) (hι : Function.Injective ι) (m : ℕ)
    (hH : (toConv (AlgHom.id R H)) ^ m = 1) : (toConv (AlgHom.id R G)) ^ m = 1 := by

  have h1 : convPrecomp H ι ((toConv (AlgHom.id R H)) ^ m) =
      convPostcomp G (ι : G →ₐ[R] H) ((toConv (AlgHom.id R G)) ^ m) := by
    rw [map_pow, map_pow]
    congr 1
  rw [hH, map_one] at h1
  have h2 : convPostcomp G (ι : G →ₐ[R] H) ((toConv (AlgHom.id R G)) ^ m) =
      convPostcomp G (ι : G →ₐ[R] H) 1 := by rw [← h1, map_one]
  simp only [convPostcomp_apply] at h2
  have h3 := congrArg WithConv.ofConv h2
  apply WithConv.ofConv_injective
  exact AlgHom.ext fun x => hι (congrArg (fun g : G →ₐ[R] H => g x) h3)

theorem pow_eq_one_of_toConv_id_pow_eq_one (m : ℕ) (hH : (toConv (AlgHom.id R H)) ^ m = 1)
    (f : WithConv (H →ₐ[R] A)) : f ^ m = 1 := by
  have h1 : convPostcomp H f.ofConv ((toConv (AlgHom.id R H)) ^ m) = f ^ m := by
    rw [map_pow]
    congr 1
  rw [← h1, hH, map_one]

end Convolution
p2m_reactivate "P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one.HopfAlgebra.RaynaudConservative.HopfIdealQuotient"

section Generic

variable {R : Type u} [CommRing R] [IsDomain R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

open scoped nonZeroDivisors

theorem eq_zero_of_one_tmul_eq_zero {M : Type*} [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] {m : M} (h : (1 : K) ⊗ₜ[R] m = 0) : m = 0 := by
  have h' : (TensorProduct.mk R K M 1) m = 0 := h
  rw [IsLocalizedModule.eq_zero_iff (R⁰) (TensorProduct.mk R K M 1)] at h'
  obtain ⟨s, hs⟩ := h'
  rw [Submonoid.smul_def] at hs
  exact (smul_eq_zero_iff_right (nonZeroDivisors.ne_zero s.2)).1 hs

theorem injective_of_baseChange_injective {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.IsTorsionFree R M] (f : M →ₗ[R] N)
    (hf : Function.Injective (f.baseChange K)) : Function.Injective f := by
  intro x y hxy
  have h1 : f.baseChange K ((1 : K) ⊗ₜ[R] x) = f.baseChange K ((1 : K) ⊗ₜ[R] y) := by
    simp [LinearMap.baseChange_tmul, hxy]
  have h2 := hf h1
  rw [← sub_eq_zero, ← TensorProduct.tmul_sub] at h2
  exact sub_eq_zero.1 (eq_zero_of_one_tmul_eq_zero K h2)

def GenSurj {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M → N) : Prop :=
  ∀ y : N, ∃ c : R, c ≠ 0 ∧ ∃ x : M, f x = c • y

theorem genSurj_of_baseChange_surjective {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N] (f : M →ₗ[R] N)
    (hf : Function.Surjective (f.baseChange K)) : GenSurj (R := R) f := by
  intro y
  obtain ⟨t, ht⟩ := hf ((1 : K) ⊗ₜ[R] y)
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalizedModule.surj (R⁰) (TensorProduct.mk R K M 1) t
  simp only [TensorProduct.mk_apply] at hxs
  refine ⟨s, nonZeroDivisors.ne_zero s.2, x, ?_⟩
  have h1 : f.baseChange K ((s : R) • t) = (s : R) • ((1 : K) ⊗ₜ[R] y) := by
    rw [LinearMap.map_smul_of_tower, ht]
  rw [Submonoid.smul_def] at hxs
  rw [hxs, LinearMap.baseChange_tmul, ← TensorProduct.tmul_smul] at h1
  rw [← sub_eq_zero, ← TensorProduct.tmul_sub] at h1
  exact sub_eq_zero.1 (eq_zero_of_one_tmul_eq_zero K h1)

theorem baseChange_surjective_of_genSurj {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : GenSurj (R := R) f) :
    Function.Surjective (f.baseChange K) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro z -
  induction z with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul k y =>
      obtain ⟨c, hc, x, hx⟩ := hf y
      have hcK : algebraMap R K c ≠ 0 := by
        intro h
        exact hc (IsFractionRing.injective R K (by rw [h, map_zero]))
      have h0 : f.baseChange K ((1 : K) ⊗ₜ[R] x) = (algebraMap R K c) ⊗ₜ[R] y := by
        rw [LinearMap.baseChange_tmul, hx, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
          Algebra.smul_def, mul_one]
      have h1 : k ⊗ₜ[R] y = (k * (algebraMap R K c)⁻¹) • f.baseChange K ((1 : K) ⊗ₜ[R] x) := by
        rw [h0, TensorProduct.smul_tmul', smul_eq_mul, mul_assoc, inv_mul_cancel₀ hcK, mul_one]
      rw [h1]
      exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)

variable {K}

theorem one_tmul_ne_zero {M : Type*} [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
    {m : M} (hm : m ≠ 0) : (1 : K) ⊗ₜ[R] m ≠ 0 := fun h => hm (eq_zero_of_one_tmul_eq_zero K h)

variable (K)

theorem finrank_baseChange_lt_of_injective {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] (f : N →ₗ[R] M) (hf : Function.Injective f)
    (hsat : ∀ (c : R) (m : M), c ≠ 0 → c • m ∈ LinearMap.range f → m ∈ LinearMap.range f)
    (hne : LinearMap.range f ≠ ⊤) :
    Module.finrank K (K ⊗[R] N) < Module.finrank K (K ⊗[R] M) := by
  haveI : Module.Flat R K := IsLocalization.flat K (R⁰)
  set P := M ⧸ LinearMap.range f
  set g : M →ₗ[R] P := (LinearMap.range f).mkQ

  haveI : Module.IsTorsionFree R P := by
    refine ⟨fun c hc => ?_⟩
    intro a b hab
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ b
    have hc0 : c ≠ 0 := hc.ne_zero
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    apply hsat c _ hc0
    have : (LinearMap.range f).mkQ (c • a) = (LinearMap.range f).mkQ (c • b) := by
      simpa using hab
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      ← smul_sub] at this
    exact this
  have hP : ∃ q : P, q ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    rw [eq_top_iff]
    rintro m -
    have := h (g m)
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  obtain ⟨q, hq⟩ := hP

  have hgs : Function.Surjective (g.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective K (Submodule.mkQ_surjective _)
  have hfi : Function.Injective (f.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hf
  have hle : LinearMap.range (f.baseChange K) ≤ LinearMap.ker (g.baseChange K) := by
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    induction z with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
    | tmul k x =>
        rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
        have : g (f x) = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact LinearMap.mem_range_self f x
        rw [this, TensorProduct.tmul_zero]
  have h1 : Module.finrank K (K ⊗[R] N) = Module.finrank K (LinearMap.range (f.baseChange K)) :=
    (LinearMap.finrank_range_of_inj hfi).symm
  have h2 : Module.finrank K (LinearMap.range (f.baseChange K)) ≤
      Module.finrank K (LinearMap.ker (g.baseChange K)) := Submodule.finrank_mono hle
  have h3 := LinearMap.finrank_range_add_finrank_ker (g.baseChange K)
  have h4 : Module.finrank K (LinearMap.range (g.baseChange K)) = Module.finrank K (K ⊗[R] P) := by
    rw [LinearMap.range_eq_top.2 hgs, finrank_top]
  have h5 : 0 < Module.finrank K (K ⊗[R] P) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨(1 : K) ⊗ₜ[R] q, one_tmul_ne_zero hq⟩
  omega

theorem finrank_baseChange_lt_of_surjective {M P : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] [Module.Finite R M] [Module.IsTorsionFree R M] (g : M →ₗ[R] P)
    (hg : Function.Surjective g) {x : M} (hx : x ≠ 0) (hgx : g x = 0) :
    Module.finrank K (K ⊗[R] P) < Module.finrank K (K ⊗[R] M) := by
  have hgs : Function.Surjective (g.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective K hg
  have h3 := LinearMap.finrank_range_add_finrank_ker (g.baseChange K)
  have h4 : Module.finrank K (LinearMap.range (g.baseChange K)) = Module.finrank K (K ⊗[R] P) := by
    rw [LinearMap.range_eq_top.2 hgs, finrank_top]
  have h5 : 0 < Module.finrank K (LinearMap.ker (g.baseChange K)) := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    have hmem : (1 : K) ⊗ₜ[R] x ∈ LinearMap.ker (g.baseChange K) := by
      rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, hgx, TensorProduct.tmul_zero]
    rw [h0, Submodule.mem_bot] at hmem
    exact one_tmul_ne_zero (K := K) hx hmem
  omega

end Generic
p2m_reactivate "P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one.HopfAlgebra.RaynaudConservative.HopfIdealQuotient"

section Devissage

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
variable {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']

theorem isTorsionFree_quotient_of_saturated (I : Ideal H')
    (hsat : ∀ (c : R) (x : H'), c ≠ 0 → c • x ∈ I → x ∈ I) :
    Module.IsTorsionFree R (H' ⧸ I) := by
  refine ⟨fun c hc => ?_⟩
  intro a b hab
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hc0 : c ≠ 0 := hc.ne_zero
  rw [Ideal.Quotient.eq]
  apply hsat c _ hc0
  have hab' : Ideal.Quotient.mk I (c • a) = Ideal.Quotient.mk I (c • b) := by
    have h1 : ∀ y : H', Ideal.Quotient.mk I (c • y) = c • Ideal.Quotient.mk I y := fun y => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]
    rw [h1, h1]
    exact hab
  rw [Ideal.Quotient.eq, ← smul_sub] at hab'
  exact hab'

theorem finite_quotient (I : Ideal H') : Module.Finite R (H' ⧸ I) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ_surjective R I)

theorem flat_of_isTorsionFree (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Flat R M := by
  haveI : Module.Free R M := Module.free_of_finite_type_torsion_free'
  infer_instance

variable (φ : H →ₐc[R] H') (I' : Ideal H')

def comapIdeal : Ideal H := I'.comap (φ : H →ₐ[R] H')

theorem mem_comapIdeal {x : H} : x ∈ comapIdeal φ I' ↔ φ x ∈ I' := Ideal.mem_comap

theorem comapIdeal_saturated (hsat : ∀ (c : R) (x : H'), c ≠ 0 → c • x ∈ I' → x ∈ I') :
    ∀ (c : R) (x : H), c ≠ 0 → c • x ∈ comapIdeal φ I' → x ∈ comapIdeal φ I' := by
  intro c x hc hx
  rw [mem_comapIdeal] at hx ⊢
  rw [map_smul] at hx
  exact hsat c _ hc hx

def quotMap : H ⧸ comapIdeal φ I' →ₐ[R] H' ⧸ I' :=
  Ideal.quotientMapₐ I' (φ : H →ₐ[R] H') le_rfl

@[scoped simp] theorem quotMap_mk (x : H) :
    quotMap φ I' (Ideal.Quotient.mk (comapIdeal φ I') x) = Ideal.Quotient.mk I' (φ x) := rfl

theorem quotMap_injective : Function.Injective (quotMap φ I') := by
  intro a b hab
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [quotMap_mk, quotMap_mk, Ideal.Quotient.eq] at hab
  rw [Ideal.Quotient.eq, mem_comapIdeal, map_sub]
  exact hab

theorem isHopfIdeal_comapIdeal [hI' : IsHopfIdeal' R I']
    (hsat : ∀ (c : R) (x : H'), c ≠ 0 → c • x ∈ I' → x ∈ I') :
    IsHopfIdeal' R (comapIdeal φ I') := by
  haveI : Module.IsTorsionFree R (H' ⧸ I') := isTorsionFree_quotient_of_saturated I' hsat
  haveI : Module.IsTorsionFree R (H ⧸ comapIdeal φ I') :=
    isTorsionFree_quotient_of_saturated _ (comapIdeal_saturated φ I' hsat)
  haveI : Module.Finite R (H' ⧸ I') := finite_quotient I'
  haveI : Module.Finite R (H ⧸ comapIdeal φ I') := finite_quotient _
  haveI : Module.Flat R (H' ⧸ I') := flat_of_isTorsionFree _
  haveI : Module.Flat R (H ⧸ comapIdeal φ I') := flat_of_isTorsionFree _
  refine ⟨?_, ?_, ?_⟩
  · intro x hx

    set ψ := quotMap φ I'
    have hinj : Function.Injective (Algebra.TensorProduct.map ψ ψ) := by
      have h1 : Function.Injective (ψ.toLinearMap.rTensor (H ⧸ comapIdeal φ I')) :=
        Module.Flat.rTensor_preserves_injective_linearMap _ (quotMap_injective φ I')
      have h2 : Function.Injective (ψ.toLinearMap.lTensor (H' ⧸ I')) :=
        Module.Flat.lTensor_preserves_injective_linearMap _ (quotMap_injective φ I')
      have : (Algebra.TensorProduct.map ψ ψ : _ → _) =
          (ψ.toLinearMap.lTensor (H' ⧸ I')) ∘ (ψ.toLinearMap.rTensor (H ⧸ comapIdeal φ I')) := by
        funext z
        change TensorProduct.map ψ.toLinearMap ψ.toLinearMap z = _
        rw [← LinearMap.lTensor_comp_rTensor]
        rfl
      rw [this]
      exact h2.comp h1
    apply hinj
    rw [map_zero]
    have hnat : ∀ z : H ⊗[R] H, Algebra.TensorProduct.map ψ ψ
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (comapIdeal φ I'))
          (Ideal.Quotient.mkₐ R (comapIdeal φ I')) z) =
        Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I') (Ideal.Quotient.mkₐ R I')
          (Algebra.TensorProduct.map (φ : H →ₐ[R] H') (φ : H →ₐ[R] H') z) := by
      intro z
      induction z with
      | zero => simp
      | tmul a b => rfl
      | add z w hz hw => simp only [map_add, hz, hw]
    rw [hnat]
    have hco : Algebra.TensorProduct.map (φ : H →ₐ[R] H') (φ : H →ₐ[R] H')
        (Coalgebra.comul (R := R) x) = Coalgebra.comul (R := R) (φ x) :=
      congrArg (fun g : H →ₐ[R] H' ⊗[R] H' => g x) (BialgHom.map_comp_comulAlgHom φ)
    rw [hco]
    exact hI'.map_mkₐ_comul_eq_zero _ ((mem_comapIdeal φ I').1 hx)
  · intro x hx
    have h1 : Coalgebra.counit (R := R) (φ x) = Coalgebra.counit (R := R) x :=
      CoalgHomClass.counit_comp_apply φ x
    rw [← h1]
    exact hI'.counit_eq_zero _ ((mem_comapIdeal φ I').1 hx)
  · intro x hx
    rw [mem_comapIdeal, HopfAlgebra.map_antipode φ]
    exact hI'.antipode_mem _ ((mem_comapIdeal φ I').1 hx)

variable [hI' : IsHopfIdeal' R I'] [hI : IsHopfIdeal' R (comapIdeal φ I')]

noncomputable def quotBialgHom : H ⧸ comapIdeal φ I' →ₐc[R] H' ⧸ I' :=
  BialgHom.ofAlgHom (quotMap φ I')
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      rw [AlgHom.comp_assoc, HopfIdealQuotient.counitAlgHom_eq, HopfIdealQuotient.counitAlgHom_eq,
        HopfIdealQuotient.counit_comp_mkₐ]
      refine AlgHom.ext fun x => ?_
      change HopfIdealQuotient.counit R I' (quotMap φ I' (Ideal.Quotient.mk _ x)) = _
      rw [quotMap_mk, HopfIdealQuotient.counit_mk]
      exact CoalgHomClass.counit_comp_apply φ x)
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      rw [AlgHom.comp_assoc, AlgHom.comp_assoc, HopfIdealQuotient.comulAlgHom_eq,
        HopfIdealQuotient.comulAlgHom_eq, HopfIdealQuotient.comul_comp_mkₐ, ← AlgHom.comp_assoc,
        ← Algebra.TensorProduct.map_comp]
      refine AlgHom.ext fun x => ?_
      change Algebra.TensorProduct.map ((quotMap φ I').comp (Ideal.Quotient.mkₐ R _))
          ((quotMap φ I').comp (Ideal.Quotient.mkₐ R _)) (Coalgebra.comul (R := R) x) =
        HopfIdealQuotient.comul R I' (quotMap φ I' (Ideal.Quotient.mk _ x))
      rw [quotMap_mk, HopfIdealQuotient.comul_mk]
      have hco : Algebra.TensorProduct.map (φ : H →ₐ[R] H') (φ : H →ₐ[R] H')
          (Coalgebra.comul (R := R) x) = Coalgebra.comul (R := R) (φ x) :=
        congrArg (fun g : H →ₐ[R] H' ⊗[R] H' => g x) (BialgHom.map_comp_comulAlgHom φ)
      rw [← hco]
      change _ = ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I') (Ideal.Quotient.mkₐ R I')).comp
        (Algebra.TensorProduct.map (φ : H →ₐ[R] H') (φ : H →ₐ[R] H'))) (Coalgebra.comul (R := R) x)
      rw [← Algebra.TensorProduct.map_comp]
      rfl)

@[scoped simp] theorem quotBialgHom_mk (x : H) :
    quotBialgHom φ I' (Ideal.Quotient.mk (comapIdeal φ I') x) = Ideal.Quotient.mk I' (φ x) := rfl

theorem quotBialgHom_injective : Function.Injective (quotBialgHom φ I') := quotMap_injective φ I'

theorem quotBialgHom_comm :
    ((HopfIdealQuotient.quotientBialgHom R I' : H' →ₐc[R] H' ⧸ I') : H' →ₐ[R] H' ⧸ I').comp
        (φ : H →ₐ[R] H') =
      ((quotBialgHom φ I' : H ⧸ comapIdeal φ I' →ₐc[R] H' ⧸ I') : H ⧸ comapIdeal φ I' →ₐ[R] H' ⧸ I').comp
        ((HopfIdealQuotient.quotientBialgHom R (comapIdeal φ I') : H →ₐc[R] H ⧸ comapIdeal φ I') :
          H →ₐ[R] H ⧸ comapIdeal φ I') :=
  AlgHom.ext fun _ => rfl

noncomputable abbrev πQ : H →ₐc[R] H ⧸ comapIdeal φ I' :=
  HopfIdealQuotient.quotientBialgHom R (comapIdeal φ I')

noncomputable abbrev πQ' (R : Type u) [CommRing R] {H' : Type v} [CommRing H'] [HopfAlgebra R H']
    (I' : Ideal H') [IsHopfIdeal' R I'] : H' →ₐc[R] H' ⧸ I' :=
  HopfIdealQuotient.quotientBialgHom R I'

theorem coaction_comp :
    (coaction (πQ' R I')).comp (φ : H →ₐ[R] H') =
      (Algebra.TensorProduct.map (φ : H →ₐ[R] H')
          ((quotBialgHom φ I' : H ⧸ comapIdeal φ I' →ₐc[R] H' ⧸ I') :
            H ⧸ comapIdeal φ I' →ₐ[R] H' ⧸ I')).comp (coaction (πQ φ I')) := by
  unfold coaction
  rw [AlgHom.comp_assoc, ← BialgHom.map_comp_comulAlgHom φ, ← AlgHom.comp_assoc,
    ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
    AlgHom.id_comp, AlgHom.comp_id]
  rfl

theorem coaction_apply_φ (x : H) :
    coaction (πQ' R I') (φ x) =
      Algebra.TensorProduct.map (φ : H →ₐ[R] H')
        ((quotBialgHom φ I' : H ⧸ comapIdeal φ I' →ₐc[R] H' ⧸ I') :
          H ⧸ comapIdeal φ I' →ₐ[R] H' ⧸ I') (coaction (πQ φ I') x) := by
  have := congrArg (fun g : H →ₐ[R] H' ⊗[R] (H' ⧸ I') => g x) (coaction_comp φ I')
  simpa using this

theorem map_mem_hopfKer {x : H} (hx : x ∈ hopfKer (πQ φ I')) : φ x ∈ hopfKer (πQ' R I') := by
  rw [mem_hopfKer_iff] at hx ⊢
  rw [coaction_apply_φ, hx]
  simp

theorem map_φ_ψ_injective (hφ : Function.Injective φ) [Module.Flat R (H ⧸ comapIdeal φ I')] :
    Function.Injective (Algebra.TensorProduct.map (φ : H →ₐ[R] H')
        ((quotBialgHom φ I' : H ⧸ comapIdeal φ I' →ₐc[R] H' ⧸ I') :
          H ⧸ comapIdeal φ I' →ₐ[R] H' ⧸ I')) := by
  set ψ : H ⧸ comapIdeal φ I' →ₐ[R] H' ⧸ I' :=
    ((quotBialgHom φ I' : H ⧸ comapIdeal φ I' →ₐc[R] H' ⧸ I') : H ⧸ comapIdeal φ I' →ₐ[R] H' ⧸ I')
  have h1 : Function.Injective ((φ : H →ₐ[R] H').toLinearMap.rTensor (H ⧸ comapIdeal φ I')) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hφ
  have h2 : Function.Injective (ψ.toLinearMap.lTensor H') :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (quotBialgHom_injective φ I')
  have : (Algebra.TensorProduct.map (φ : H →ₐ[R] H') ψ : _ → _) =
      (ψ.toLinearMap.lTensor H') ∘ ((φ : H →ₐ[R] H').toLinearMap.rTensor (H ⧸ comapIdeal φ I')) := by
    funext z
    change TensorProduct.map (φ : H →ₐ[R] H').toLinearMap ψ.toLinearMap z = _
    rw [← LinearMap.lTensor_comp_rTensor]
    rfl
  rw [this]
  exact h2.comp h1

theorem mem_hopfKer_of_map_mem (hφ : Function.Injective φ) [Module.Flat R (H ⧸ comapIdeal φ I')]
    {x : H} (hx : φ x ∈ hopfKer (πQ' R I')) : x ∈ hopfKer (πQ φ I') := by
  rw [mem_hopfKer_iff] at hx ⊢
  apply map_φ_ψ_injective φ I' hφ
  rw [← coaction_apply_φ, hx]
  simp

noncomputable def kerMap : ↥(hopfKer (πQ φ I')) →ₐ[R] ↥(hopfKer (πQ' R I')) :=
  ((φ : H →ₐ[R] H').comp (hopfKer (πQ φ I')).val).codRestrict (hopfKer (πQ' R I'))
    (fun x => map_mem_hopfKer φ I' x.2)

@[scoped simp] theorem coe_kerMap (x : ↥(hopfKer (πQ φ I'))) : (kerMap φ I' x : H') = φ x := rfl

theorem kerMap_injective (hφ : Function.Injective φ) : Function.Injective (kerMap φ I') := by
  intro a b hab
  apply Subtype.ext
  apply hφ
  have := congrArg Subtype.val hab
  simpa using this

variable [Coalgebra.IsCocomm R H] [Coalgebra.IsCocomm R H']
variable [Module.Flat R (H ⧸ comapIdeal φ I')] [Module.Flat R (H' ⧸ I')]
variable [Module.Flat R ↥(hopfKer (πQ φ I'))] [Module.Flat R ↥(hopfKer (πQ' R I'))]

noncomputable def kerBialgHom : ↥(hopfKer (πQ φ I')) →ₐc[R] ↥(hopfKer (πQ' R I')) :=
  BialgHom.ofAlgHom (kerMap φ I')
    (by
      refine AlgHom.ext fun x => ?_
      change Coalgebra.counit (R := R) (kerMap φ I' x) = Coalgebra.counit (R := R) x
      rw [HopfKerHopf.counit_coe, HopfKerHopf.counit_coe, coe_kerMap]
      exact CoalgHomClass.counit_comp_apply φ (x : H))
    (by
      refine AlgHom.ext fun x => ?_
      change Algebra.TensorProduct.map (kerMap φ I') (kerMap φ I') (Coalgebra.comul (R := R) x) =
        Coalgebra.comul (R := R) (kerMap φ I' x)
      apply HopfKerHopf.ι₂_injective (πQ' R I')
      rw [HopfKerHopf.ι₂_comul]
      have hnat : ∀ z : ↥(hopfKer (πQ φ I')) ⊗[R] ↥(hopfKer (πQ φ I')),
          HopfKerHopf.ι₂ (πQ' R I') (Algebra.TensorProduct.map (kerMap φ I') (kerMap φ I') z) =
            Algebra.TensorProduct.map (φ : H →ₐ[R] H') (φ : H →ₐ[R] H')
              (HopfKerHopf.ι₂ (πQ φ I') z) := by
        intro z
        induction z with
        | zero => simp
        | tmul a b => rfl
        | add z w hz hw => simp only [map_add, hz, hw]
      rw [hnat, HopfKerHopf.ι₂_comul, coe_kerMap]
      exact congrArg (fun g : H →ₐ[R] H' ⊗[R] H' => g (x : H)) (BialgHom.map_comp_comulAlgHom φ))

@[scoped simp] theorem coe_kerBialgHom (x : ↥(hopfKer (πQ φ I'))) : ((kerBialgHom φ I' x : ↥(hopfKer (πQ' R I'))) : H') = φ x :=
  rfl

theorem kerBialgHom_injective (hφ : Function.Injective φ) : Function.Injective (kerBialgHom φ I') :=
  kerMap_injective φ I' hφ

end Devissage
p2m_reactivate "P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one.HopfAlgebra.RaynaudConservative.HopfIdealQuotient"

section Induction

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
variable (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R)) (n : ℕ)

open scoped nonZeroDivisors

def IsSimple (H' : Type v) [CommRing H'] [HopfAlgebra R H'] : Prop :=
  ∀ I : Ideal H',
      (∀ (c : R) (x : H'), c ≠ 0 → c • x ∈ I → x ∈ I) →
      (∀ x ∈ I, Coalgebra.counit (R := R) x = 0) →
      (∀ x ∈ I, HopfAlgebra.antipode R x ∈ I) →
      (∀ x ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) = 0) →
      I = ⊥ ∨ I = RingHom.ker (Bialgebra.counitAlgHom R H')

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
include hp2 hunif in

theorem surjective_of_injective_of_genSurj (d : ℕ) :
    ∀ {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
      [Coalgebra.IsCocomm R H]
      {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
      [Coalgebra.IsCocomm R H'],
      Module.finrank K (K ⊗[R] H') ≤ d →
      (∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ p ^ n = 1) →
      (∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H' →ₐ[R] T)), f ^ p ^ n = 1) →
      ∀ (φ : H →ₐc[R] H'), Function.Injective φ →
        Function.Surjective ((φ : H →ₐ[R] H').toLinearMap.baseChange K) → Function.Surjective φ := by
  induction d with
  | zero =>
      intro H _ _ _ _ _ H' _ _ _ _ _ hd hH hH' φ hφ hφK
      exfalso
      have h1' : (1 : H') ≠ 0 := fun h => one_ne_zero (α := R) (by
        have := Bialgebra.counit_one (R := R) (A := H')
        rw [h, map_zero] at this
        exact this.symm)
      have h1 : 0 < Module.finrank K (K ⊗[R] H') := by
        rw [Module.finrank_pos_iff_exists_ne_zero]
        exact ⟨(1 : K) ⊗ₜ[R] (1 : H'), one_tmul_ne_zero h1'⟩
      omega
  | succ d ih =>
      intro H _ _ _ _ _ H' _ _ _ _ _ hd hH hH' φ hφ hφK
      by_cases hs : IsSimple (R := R) H'
      · exact HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple K p hp2
          hunif n hH hH' hs φ hφ hφK

      simp only [IsSimple, not_forall, not_or, exists_prop] at hs
      obtain ⟨I', hsat, hcou, hant, hcom, hbot, htop⟩ := hs
      haveI hI' : IsHopfIdeal' R I' := ⟨hcom, hcou, hant⟩
      haveI hI : IsHopfIdeal' R (comapIdeal φ I') := isHopfIdeal_comapIdeal φ I' hsat

      haveI : Module.IsTorsionFree R (H' ⧸ I') := isTorsionFree_quotient_of_saturated I' hsat
      haveI : Module.IsTorsionFree R (H ⧸ comapIdeal φ I') :=
        isTorsionFree_quotient_of_saturated _ (comapIdeal_saturated φ I' hsat)
      haveI : Module.Finite R (H' ⧸ I') := finite_quotient I'
      haveI : Module.Finite R (H ⧸ comapIdeal φ I') := finite_quotient _
      haveI : Module.Flat R (H' ⧸ I') := flat_of_isTorsionFree _
      haveI : Module.Flat R (H ⧸ comapIdeal φ I') := flat_of_isTorsionFree _

      haveI : IsNoetherianRing R := inferInstance
      haveI : Module.Finite R ↥(hopfKer (πQ' R I')) := by
        haveI : IsNoetherian R H' := isNoetherian_of_isNoetherianRing_of_finite R H'
        exact Module.Finite.of_injective (hopfKer (πQ' R I')).val.toLinearMap Subtype.val_injective
      haveI : Module.Finite R ↥(hopfKer (πQ φ I')) := by
        haveI : IsNoetherian R H := isNoetherian_of_isNoetherianRing_of_finite R H
        exact Module.Finite.of_injective (hopfKer (πQ φ I')).val.toLinearMap Subtype.val_injective
      haveI : Module.IsTorsionFree R ↥(hopfKer (πQ' R I')) :=
        Subtype.val_injective.moduleIsTorsionFree (fun x : ↥(hopfKer (πQ' R I')) => (x : H'))
          (fun _ _ => rfl)
      haveI : Module.IsTorsionFree R ↥(hopfKer (πQ φ I')) :=
        Subtype.val_injective.moduleIsTorsionFree (fun x : ↥(hopfKer (πQ φ I')) => (x : H))
          (fun _ _ => rfl)
      haveI : Module.Flat R ↥(hopfKer (πQ' R I')) := flat_of_isTorsionFree _
      haveI : Module.Flat R ↥(hopfKer (πQ φ I')) := flat_of_isTorsionFree _

      have hgs : GenSurj (R := R) φ :=
        genSurj_of_baseChange_surjective K (φ : H →ₐ[R] H').toLinearMap hφK

      set ψ := quotBialgHom φ I' with hψdef
      have hψinj : Function.Injective ψ := quotBialgHom_injective φ I'
      have hψgs : GenSurj (R := R) ψ := by
        intro y
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        obtain ⟨c, hc, x, hx⟩ := hgs y
        refine ⟨c, hc, Ideal.Quotient.mk _ x, ?_⟩
        rw [quotBialgHom_mk, hx, Algebra.smul_def, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]
      have hdQ : Module.finrank K (K ⊗[R] (H' ⧸ I')) ≤ d := by
        have hx : ∃ x ∈ I', x ≠ 0 := by
          by_contra h
          push Not at h
          exact hbot ((Submodule.eq_bot_iff _).2 h)
        obtain ⟨x, hxI, hx0⟩ := hx
        have := finrank_baseChange_lt_of_surjective K (Ideal.Quotient.mkₐ R I').toLinearMap
          (Ideal.Quotient.mkₐ_surjective R I') hx0
          (Ideal.Quotient.eq_zero_iff_mem.2 hxI)
        omega
      have hQ : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H ⧸ comapIdeal φ I' →ₐ[R] T)),
          f ^ p ^ n = 1 := fun T _ _ f =>
        pow_eq_one_of_surjective (πQ φ I') (HopfIdealQuotient.quotientBialgHom_surjective R _) _
          (hH T) f
      have hQ' : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H' ⧸ I' →ₐ[R] T)),
          f ^ p ^ n = 1 := fun T _ _ f =>
        pow_eq_one_of_surjective (πQ' R I') (HopfIdealQuotient.quotientBialgHom_surjective R _) _
          (hH' T) f
      have hψsurj : Function.Surjective ψ :=
        ih (H := H ⧸ comapIdeal φ I') (H' := H' ⧸ I') hdQ hQ hQ' ψ hψinj
          (baseChange_surjective_of_genSurj K (ψ : H ⧸ comapIdeal φ I' →ₐ[R] H' ⧸ I').toLinearMap hψgs)

      set κ := kerBialgHom φ I' with hκdef
      have hκinj : Function.Injective κ := kerBialgHom_injective φ I' hφ
      have hκgs : GenSurj (R := R) κ := by
        intro y
        obtain ⟨c, hc, x, hx⟩ := hgs (y : H')
        have hxK : x ∈ hopfKer (πQ φ I') := by
          apply mem_hopfKer_of_map_mem φ I' hφ
          rw [hx]
          exact Subalgebra.smul_mem _ y.2 c
        refine ⟨c, hc, ⟨x, hxK⟩, Subtype.ext ?_⟩
        rw [coe_kerBialgHom]
        simpa using hx
      have hdS : Module.finrank K (K ⊗[R] ↥(hopfKer (πQ' R I'))) ≤ d := by
        have hlt := finrank_baseChange_lt_of_injective K (hopfKer (πQ' R I')).val.toLinearMap
          Subtype.val_injective
          (by
            intro c m hc hm
            have hrange : ∀ z : H', z ∈ LinearMap.range (hopfKer (πQ' R I')).val.toLinearMap ↔
                z ∈ hopfKer (πQ' R I') := fun z =>
              ⟨fun ⟨w, hw⟩ => hw ▸ w.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
            rw [hrange] at hm ⊢
            rw [mem_hopfKer_iff] at hm ⊢
            rw [map_smul, ← TensorProduct.smul_tmul'] at hm
            have hreg : IsSMulRegular (H' ⊗[R] (H' ⧸ I')) c := IsSMulRegular.of_ne_zero hc
            exact hreg hm)
          (by
            intro htop'
            apply htop

            have hall : ∀ z : H', z ∈ hopfKer (πQ' R I') := fun z => by
              have : z ∈ LinearMap.range (hopfKer (πQ' R I')).val.toLinearMap := htop' ▸ Submodule.mem_top
              obtain ⟨w, hw⟩ := this
              exact hw ▸ w.2
            apply le_antisymm
            · intro z hz
              exact (RingHom.mem_ker).2 (hcou z hz)
            · intro z hz
              rw [RingHom.mem_ker] at hz
              have hz' : Coalgebra.counit (R := R) z = 0 := hz
              have hcz := hall z
              rw [mem_hopfKer_iff] at hcz

              have h1 := congrArg (Algebra.TensorProduct.lift ((Algebra.ofId R (H' ⧸ I')).comp
                (Bialgebra.counitAlgHom R H')) (AlgHom.id R (H' ⧸ I')) (fun _ _ => .all _ _)) hcz
              rw [coaction_apply] at h1
              simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, map_one, mul_one,
                Bialgebra.counitAlgHom_apply, hz', map_zero] at h1

              have h2 : Algebra.TensorProduct.lift ((Algebra.ofId R (H' ⧸ I')).comp
                  (Bialgebra.counitAlgHom R H')) (AlgHom.id R (H' ⧸ I')) (fun _ _ => .all _ _)
                  (Algebra.TensorProduct.map (AlgHom.id R H') ((πQ' R I' : H' →ₐc[R] H' ⧸ I') : H' →ₐ[R] H' ⧸ I')
                    (Coalgebra.comul (R := R) z)) = Ideal.Quotient.mk I' z := by
                have e1 : ∀ w : H' ⊗[R] H', Algebra.TensorProduct.lift ((Algebra.ofId R (H' ⧸ I')).comp
                    (Bialgebra.counitAlgHom R H')) (AlgHom.id R (H' ⧸ I')) (fun _ _ => .all _ _)
                    (Algebra.TensorProduct.map (AlgHom.id R H')
                      ((πQ' R I' : H' →ₐc[R] H' ⧸ I') : H' →ₐ[R] H' ⧸ I') w) =
                    Ideal.Quotient.mk I' (Algebra.TensorProduct.lid R H'
                      ((Coalgebra.counit (R := R) (A := H')).rTensor H' w)) := by
                  intro w
                  induction w with
                  | zero => simp
                  | tmul a b =>
                      simp [Algebra.ofId_apply, Algebra.smul_def, Ideal.Quotient.mk_algebraMap]
                  | add x y hx hy => simp only [map_add, hx, hy]
                rw [e1, Coalgebra.rTensor_counit_comul]
                simp
              rw [h2] at h1
              exact Ideal.Quotient.eq_zero_iff_mem.1 h1)
        omega
      have hS : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (↥(hopfKer (πQ φ I')) →ₐ[R] T)),
          f ^ p ^ n = 1 := fun T _ _ f =>
        pow_eq_one_of_toConv_id_pow_eq_one _
          (toConv_id_pow_eq_one_of_injective (hopfKerVal (πQ φ I')) (hopfKerVal_injective _) _
            (hH H (toConv (AlgHom.id R H)))) f
      have hS' : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (↥(hopfKer (πQ' R I')) →ₐ[R] T)),
          f ^ p ^ n = 1 := fun T _ _ f =>
        pow_eq_one_of_toConv_id_pow_eq_one _
          (toConv_id_pow_eq_one_of_injective (hopfKerVal (πQ' R I')) (hopfKerVal_injective _) _
            (hH' H' (toConv (AlgHom.id R H')))) f
      have hκsurj : Function.Surjective κ :=
        ih (H := ↥(hopfKer (πQ φ I'))) (H' := ↥(hopfKer (πQ' R I'))) hdS hS hS' κ hκinj
          (baseChange_surjective_of_genSurj K
            (κ : ↥(hopfKer (πQ φ I')) →ₐ[R] ↥(hopfKer (πQ' R I'))).toLinearMap hκgs)

      exact HopfAlgebra.surjective_of_bijective_of_bijOn_hopfKer φ (πQ φ I') (πQ' R I') ψ
        (HopfIdealQuotient.quotientBialgHom_surjective R _) (HopfIdealQuotient.quotientBialgHom_surjective R _)
        (quotBialgHom_comm φ I') ⟨hψinj, hψsurj⟩
        ⟨fun x hx => map_mem_hopfKer φ I' hx, hφ.injOn,
          fun y hy => by
            obtain ⟨x, hx⟩ := hκsurj ⟨y, hy⟩
            exact ⟨x, x.2, by have h__af := congrArg Subtype.val hx; simp at h__af; exact h__af⟩⟩

end Induction
p2m_reactivate "P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one.HopfAlgebra.RaynaudConservative.HopfIdealQuotient"

end HopfAlgebra.RaynaudConservative
p2m_reactivate "P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one.HopfAlgebra.RaynaudConservative.HopfIdealQuotient P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one.HopfAlgebra P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one.HopfAlgebra.RaynaudConservative"
p2m_reactivate "P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one.HopfAlgebra.RaynaudConservative.HopfIdealQuotient P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one.HopfAlgebra"

open HopfAlgebra.RaynaudConservative in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    [Coalgebra.IsCocomm R H']
    (n : ℕ)
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ p ^ n = 1)
    (hH' : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H' →ₐ[R] T)), f ^ p ^ n = 1)
    (φ : H →ₐc[R] H') (hφK : Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.baseChange K)) :
    Function.Bijective φ := by
  have hinj : Function.Injective φ :=
    injective_of_baseChange_injective K (φ : H →ₐ[R] H').toLinearMap hφK.1
  exact ⟨hinj, surjective_of_injective_of_genSurj K p hp2 hunif n _ le_rfl hH hH' φ hinj hφK.2⟩

end S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one
end P2MW
export P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one (solution)

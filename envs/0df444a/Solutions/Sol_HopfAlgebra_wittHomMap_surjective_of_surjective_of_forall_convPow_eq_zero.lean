-- Prove2me | solution 1 for HopfAlgebra.wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/15e4819f-2a79-5e86-ba40-19b57d47268e

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_HopfAlgebra_exists_mem_primitives_map_eq_of_surjective_of_forall_convPow_prime_eq_zero
import Theorems.Thm_Deformation_wittHomShift_surjective_of_forall_convPow_eq_zero
import Theorems.Thm_Deformation_convPow_prime_apply_coeff_of_mem_wittHom
import Theorems.Thm_Deformation_wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer
import Theorems.Thm_Deformation_mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero
import Theorems.Thm_Deformation_exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero
import Theorems.Thm_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply
import Theorems.Thm_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero
p2m_attr_erase "instance" "HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open scoped TensorProduct
open Function

universe u v w

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one ofAlgHom mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul mul_antipode_lTensor_comul mul_antipode_rTensor_comul_apply hopfKer HopfKerHopf.hopfKerVal_apply exists_mem_primitives_map_eq_of_surjective_of_forall_convPow_prime_eq_zero exists_mem_primitives_forall_apply_pow_eq_convPow_apply map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker"
namespace WittLevelInduction
p2m_open "HopfAlgebra"

section Quot

variable (R : Type*) [CommRing R]

class IsBiIdeal {H : Type*} [CommRing H] [Bialgebra R H] (I : Ideal H) : Prop where
  map_mkₐ_comul_eq_zero : ∀ x ∈ I,
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) x) = 0
  counit_eq_zero : ∀ x ∈ I, Coalgebra.counit (R := R) x = 0

class IsHopfIdeal' {H : Type*} [CommRing H] [HopfAlgebra R H] (I : Ideal H) : Prop
    extends IsBiIdeal R I where
  antipode_mem : ∀ x ∈ I, HopfAlgebra.antipode R x ∈ I

namespace Quot

section Bi

variable {H : Type*} [CommRing H] [Bialgebra R H] (I : Ideal H) [hI : IsBiIdeal R I]

private def _root_.HopfAlgebra.WittLevelInduction.Quot.comul : H ⧸ I →ₐ[R] (H ⧸ I) ⊗[R] (H ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (Bialgebra.comulAlgHom R H))
    (fun x hx => hI.map_mkₐ_comul_eq_zero x hx)

p2m_export "HopfAlgebra.WittLevelInduction.Quot" "comul"
theorem comul_comp_mkₐ :
    (comul R I).comp (Ideal.Quotient.mkₐ R I) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
        (Bialgebra.comulAlgHom R H) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem comul_mk (x : H) :
    comul R I (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

private def _root_.HopfAlgebra.WittLevelInduction.Quot.counit : H ⧸ I →ₐ[R] R :=
  Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom R H) (fun x hx => hI.counit_eq_zero x hx)

p2m_export "HopfAlgebra.WittLevelInduction.Quot" "counit"
theorem counit_comp_mkₐ :
    (counit R I).comp (Ideal.Quotient.mkₐ R I) = Bialgebra.counitAlgHom R H :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem counit_mk (x : H) :
    counit R I (Ideal.Quotient.mk I x) = Coalgebra.counit (R := R) x := rfl

private theorem map_apply_eq_linearMap {A B C D : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] C) (g : B →ₐ[R] D) (z : A ⊗[R] B) :
    Algebra.TensorProduct.map f g z = TensorProduct.map f.toLinearMap g.toLinearMap z := rfl

private theorem _root_.HopfAlgebra.WittLevelInduction.Quot.rTensor_counit_comul :
    (Algebra.TensorProduct.map (counit R I) (.id R (H ⧸ I))).comp (comul R I) =
      (Algebra.TensorProduct.lid R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.lid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (Bialgebra.counitAlgHom R H).toLinearMap
        (Ideal.Quotient.mkₐ R I).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.lTensor R) ∘ₗ
          ((Bialgebra.counitAlgHom R H).toLinearMap.rTensor H) from
      (LinearMap.lTensor_comp_rTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((Bialgebra.counitAlgHom R H).toLinearMap.rTensor H) (Coalgebra.comul x) = 1 ⊗ₜ x from
    Coalgebra.rTensor_counit_comul x]
  simp

p2m_export "HopfAlgebra.WittLevelInduction.Quot" "rTensor_counit_comul"
private theorem _root_.HopfAlgebra.WittLevelInduction.Quot.lTensor_counit_comul :
    (Algebra.TensorProduct.map (.id R (H ⧸ I)) (counit R I)).comp (comul R I) =
      (Algebra.TensorProduct.rid R R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.rid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap
        (Bialgebra.counitAlgHom R H).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.rTensor R) ∘ₗ
          ((Bialgebra.counitAlgHom R H).toLinearMap.lTensor H) from
      (LinearMap.rTensor_comp_lTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((Bialgebra.counitAlgHom R H).toLinearMap.lTensor H) (Coalgebra.comul x) = x ⊗ₜ 1 from
    Coalgebra.lTensor_counit_comul x]
  simp

p2m_export "HopfAlgebra.WittLevelInduction.Quot" "lTensor_counit_comul"
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
          (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R H) (.id R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hR : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.map (.id R (H ⧸ I)) (comul R I) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map π (Algebra.TensorProduct.map π π)
          (Algebra.TensorProduct.map (.id R H) (Bialgebra.comulAlgHom R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hx : comul R I (π x) = Algebra.TensorProduct.map π π (Bialgebra.comulAlgHom R H x) := by
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

scoped instance instBialgebra : Bialgebra R (H ⧸ I) :=
  Bialgebra.ofAlgHom (comul R I) (counit R I) (coassoc R I) (rTensor_counit_comul R I)
    (lTensor_counit_comul R I)

theorem comulAlgHom_eq : Bialgebra.comulAlgHom R (H ⧸ I) = comul R I := rfl

theorem counitAlgHom_eq : Bialgebra.counitAlgHom R (H ⧸ I) = counit R I := rfl

theorem coalgebra_comul_mk (x : H) :
    Coalgebra.comul (R := R) (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

def mkB : H →ₐc[R] H ⧸ I :=
  BialgHom.ofAlgHom (Ideal.Quotient.mkₐ R I) (counit_comp_mkₐ R I) (comul_comp_mkₐ R I).symm

@[scoped simp] theorem mkB_apply (x : H) : mkB R I x = Ideal.Quotient.mk I x := rfl

theorem mkB_surjective : Surjective (mkB R I) := Ideal.Quotient.mk_surjective

def factorB {J : Ideal H} [IsBiIdeal R J] (hIJ : I ≤ J) : H ⧸ I →ₐc[R] H ⧸ J :=
  BialgHom.ofAlgHom (Ideal.Quotient.factorₐ R hIJ)
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      rw [AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp_mk, counitAlgHom_eq, counitAlgHom_eq,
        counit_comp_mkₐ, counit_comp_mkₐ])
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      rw [AlgHom.comp_assoc, AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp_mk, comulAlgHom_eq,
        comulAlgHom_eq, comul_comp_mkₐ, comul_comp_mkₐ, ← AlgHom.comp_assoc,
        ← Algebra.TensorProduct.map_comp, Ideal.Quotient.factorₐ_comp_mk])

theorem factorB_surjective {J : Ideal H} [IsBiIdeal R J] (hIJ : I ≤ J) :
    Surjective (factorB R I hIJ) := Ideal.Quotient.factor_surjective hIJ

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

scoped instance instModuleFinite [Module.Finite R H] : Module.Finite R (H ⧸ I) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ_surjective R I)

end Bi

section Hopf

variable {H : Type*} [CommRing H] [HopfAlgebra R H] (I : Ideal H) [hI : IsHopfIdeal' R I]

def antipodeAlgHom' : H →ₐ[R] H :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) HopfAlgebra.antipode_one fun a b => by
    rw [HopfAlgebra.antipode_mul, mul_comm]

@[scoped simp] theorem antipodeAlgHom'_apply (x : H) : antipodeAlgHom' R x = HopfAlgebra.antipode R x :=
  rfl

private def _root_.HopfAlgebra.WittLevelInduction.Quot.antipode : H ⧸ I →ₐ[R] H ⧸ I :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R I).comp (antipodeAlgHom' R)) (fun x hx => by
    simp only [AlgHom.comp_apply, antipodeAlgHom'_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hI.antipode_mem x hx)

p2m_export "HopfAlgebra.WittLevelInduction.Quot" "antipode"
theorem antipode_comp_mkₐ :
    (antipode R I).comp (Ideal.Quotient.mkₐ R I) =
      (Ideal.Quotient.mkₐ R I).comp (antipodeAlgHom' R) :=
  Ideal.Quotient.liftₐ_comp _ _ _

private theorem lift_antipode_id_comp_map :
    (Algebra.TensorProduct.lift (antipode R I) (.id R (H ⧸ I)) fun _ _ => .all _ _).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)) =
      (Ideal.Quotient.mkₐ R I).comp
        (Algebra.TensorProduct.lift (antipodeAlgHom' R) (.id R H) fun _ _ => .all _ _) := by
  ext x
  · simp [Ideal.Quotient.mkₐ_eq_mk, antipode]
  · simp [Ideal.Quotient.mkₐ_eq_mk]

private theorem lift_id_antipode_comp_map :
    (Algebra.TensorProduct.lift (.id R (H ⧸ I)) (antipode R I) fun _ _ => .all _ _).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)) =
      (Ideal.Quotient.mkₐ R I).comp
        (Algebra.TensorProduct.lift (.id R H) (antipodeAlgHom' R) fun _ _ => .all _ _) := by
  ext x
  · simp [Ideal.Quotient.mkₐ_eq_mk]
  · simp [Ideal.Quotient.mkₐ_eq_mk, antipode]

private theorem lift_antipode_id_apply (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift (antipodeAlgHom' R) (AlgHom.id R H) (fun _ _ => .all _ _) z =
      LinearMap.mul' R H ((HopfAlgebra.antipode R).rTensor H z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

private theorem lift_id_antipode_apply (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift (AlgHom.id R H) (antipodeAlgHom' R) (fun _ _ => .all _ _) z =
      LinearMap.mul' R H ((HopfAlgebra.antipode R).lTensor H z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

private theorem lift_antipode_id_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (antipodeAlgHom' R) (.id R H) fun _ _ => .all _ _).comp
        (Bialgebra.comulAlgHom R H) = (Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H) := by
  refine AlgHom.ext fun x => ?_
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, lift_antipode_id_apply,
    HopfAlgebra.mul_antipode_rTensor_comul_apply]
  simp [Algebra.ofId_apply]

private theorem lift_id_antipode_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (.id R H) (antipodeAlgHom' R) fun _ _ => .all _ _).comp
        (Bialgebra.comulAlgHom R H) = (Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H) := by
  refine AlgHom.ext fun x => ?_
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, lift_id_antipode_apply,
    HopfAlgebra.mul_antipode_lTensor_comul_apply]
  simp [Algebra.ofId_apply]

theorem mul_antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode R I) (.id R (H ⧸ I)) fun _ _ => .all _ _).comp
        (Bialgebra.comulAlgHom R (H ⧸ I)) =
      (Algebra.ofId R (H ⧸ I)).comp (Bialgebra.counitAlgHom R (H ⧸ I)) := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [comulAlgHom_eq, counitAlgHom_eq, AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc,
    lift_antipode_id_comp_map, AlgHom.comp_assoc, lift_antipode_id_comp_comulAlgHom,
    AlgHom.comp_assoc, counit_comp_mkₐ, ← AlgHom.comp_assoc]
  congr 1

theorem mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (.id R (H ⧸ I)) (antipode R I) fun _ _ => .all _ _).comp
        (Bialgebra.comulAlgHom R (H ⧸ I)) =
      (Algebra.ofId R (H ⧸ I)).comp (Bialgebra.counitAlgHom R (H ⧸ I)) := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [comulAlgHom_eq, counitAlgHom_eq, AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc,
    lift_id_antipode_comp_map, AlgHom.comp_assoc, lift_id_antipode_comp_comulAlgHom,
    AlgHom.comp_assoc, counit_comp_mkₐ, ← AlgHom.comp_assoc]
  congr 1

scoped instance instHopfAlgebra : HopfAlgebra R (H ⧸ I) :=
  HopfAlgebra.ofAlgHom (antipode R I) (mul_antipode_rTensor_comul R I)
    (mul_antipode_lTensor_comul R I)

end Hopf

end Quot
p2m_reactivate "P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.HopfAlgebra.WittLevelInduction.Quot"

section BiIdealTools

variable {K : Type*} [Field K]
variable {H : Type*} [CommRing H] [Bialgebra K H] {H' : Type*} [CommRing H'] [Bialgebra K H']

omit [CommRing R] in

theorem map_injective_of_injective {X Y : Type*} [CommRing X] [CommRing Y] [Algebra K X]
    [Algebra K Y] (ι : X →ₐ[K] Y) (hι : Injective ι) :
    Injective (Algebra.TensorProduct.map ι ι) := by
  have h1 : Injective (ι.toLinearMap.lTensor X) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hι
  have h2 : Injective (ι.toLinearMap.rTensor Y) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hι
  have key : (Algebra.TensorProduct.map ι ι).toLinearMap =
      ι.toLinearMap.rTensor Y ∘ₗ ι.toLinearMap.lTensor X := by
    rw [LinearMap.rTensor_comp_lTensor]; rfl
  have : Injective (Algebra.TensorProduct.map ι ι).toLinearMap := by
    rw [key]; exact h2.comp h1
  exact this

abbrev kerB (f : H →ₐc[K] H') : Ideal H := RingHom.ker (f : H →ₐ[K] H')

omit [CommRing R] in

scoped instance isBiIdeal_ker (f : H →ₐc[K] H') : IsBiIdeal K (kerB f) := by
  set kf : Ideal H := RingHom.ker (f : H →ₐ[K] H')
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  ·
    let ι : H ⧸ kf →ₐ[K] H' := Ideal.kerLiftAlg (f : H →ₐ[K] H')
    have hι : Injective ι := Ideal.kerLiftAlg_injective _
    apply map_injective_of_injective ι hι
    rw [map_zero]
    have hcomp : (Algebra.TensorProduct.map ι ι).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K kf) (Ideal.Quotient.mkₐ K kf)) =
        Algebra.TensorProduct.map (f : H →ₐ[K] H') (f : H →ₐ[K] H') := by
      rw [← Algebra.TensorProduct.map_comp]
      congr 1
    have := AlgHom.congr_fun hcomp (Coalgebra.comul (R := K) x)
    rw [AlgHom.comp_apply] at this
    rw [this]
    have h2 := AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom f) x
    simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] at h2
    rw [h2]
    have hx' : f x = 0 := hx
    rw [show ((f : H →ₐ[K] H') : H → H') x = f x from rfl, hx', map_zero]
  · have hx' : f x = 0 := hx
    rw [← CoalgHomClass.counit_comp_apply (f : H →ₐc[K] H') x]
    simp [hx']

omit [CommRing R] in

scoped instance isBiIdeal_sup (I J : Ideal H) [hI : IsBiIdeal K I] [hJ : IsBiIdeal K J] :
    IsBiIdeal K (I ⊔ J) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
    have key : ∀ (L : Ideal H) [IsBiIdeal K L] (hL : L ≤ I ⊔ J) (z : H) (hz : z ∈ L),
        Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (I ⊔ J)) (Ideal.Quotient.mkₐ K (I ⊔ J))
          (Coalgebra.comul (R := K) z) = 0 := by
      intro L _ hL z hz
      have hfac : Ideal.Quotient.mkₐ K (I ⊔ J) =
          (Ideal.Quotient.factorₐ K hL).comp (Ideal.Quotient.mkₐ K L) := by
        ext; rfl
      rw [hfac, Algebra.TensorProduct.map_comp, AlgHom.comp_apply,
        IsBiIdeal.map_mkₐ_comul_eq_zero z hz, map_zero]
    rw [Coalgebra.comul.map_add, map_add, key I le_sup_left u hu, key J le_sup_right v hv,
      add_zero]
  · obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
    rw [Coalgebra.counit.map_add, hI.counit_eq_zero u hu, hJ.counit_eq_zero v hv, add_zero]

omit [CommRing R] in

def bialgHomOfCompSurjective {Q : Type*} [CommRing Q] [Bialgebra K Q]
    (f : H →ₐc[K] H') (hf : Surjective f) (g : H →ₐc[K] Q) (θ : H' →ₐ[K] Q)
    (hθ : θ.comp (f : H →ₐ[K] H') = (g : H →ₐ[K] Q)) : H' →ₐc[K] Q :=
  BialgHom.ofAlgHom θ
    (by
      have hsurj : Surjective (f : H →ₐ[K] H') := hf
      refine AlgHom.ext fun y => ?_
      obtain ⟨x, rfl⟩ := hsurj y
      have h1 := AlgHom.congr_fun hθ x
      simp only [AlgHom.comp_apply] at h1
      simp only [AlgHom.comp_apply, h1]
      change Coalgebra.counit (g x) = Coalgebra.counit (f x)
      rw [CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply])
    (by
      have hsurj : Surjective (f : H →ₐ[K] H') := hf
      refine AlgHom.ext fun y => ?_
      obtain ⟨x, rfl⟩ := hsurj y
      have h1 := AlgHom.congr_fun hθ x
      simp only [AlgHom.comp_apply] at h1
      simp only [AlgHom.comp_apply, h1, Bialgebra.comulAlgHom_apply]
      have hg := AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom g) x
      have hf' := AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom f) x
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] at hg hf'
      change _ = Coalgebra.comul (R := K) ((g : H →ₐ[K] Q) x)
      rw [← hg, ← hf', ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, hθ])

omit [CommRing R] in
@[scoped simp] theorem bialgHomOfCompSurjective_apply {Q : Type*} [CommRing Q] [Bialgebra K Q]
    (f : H →ₐc[K] H') (hf : Surjective f) (g : H →ₐc[K] Q) (θ : H' →ₐ[K] Q)
    (hθ : θ.comp (f : H →ₐ[K] H') = (g : H →ₐ[K] Q)) (y : H') :
    bialgHomOfCompSurjective f hf g θ hθ y = θ y := rfl

omit [CommRing R] in

def kerLiftB (f : H →ₐc[K] H') : (H ⧸ kerB f) →ₐc[K] H' :=
  bialgHomOfCompSurjective (Quot.mkB K (kerB f)) (Quot.mkB_surjective K _) f
    (Ideal.kerLiftAlg (f : H →ₐ[K] H')) (AlgHom.ext fun _ => rfl)

omit [CommRing R] in
theorem kerLiftB_injective (f : H →ₐc[K] H') : Injective (kerLiftB f) := by
  intro x y hxy
  exact Ideal.kerLiftAlg_injective (f : H →ₐ[K] H') hxy

omit [CommRing R] in

def kerLiftBInv (f : H →ₐc[K] H') (hf : Surjective f) : H' →ₐc[K] H ⧸ kerB f :=
  bialgHomOfCompSurjective f hf (Quot.mkB K (kerB f))
    ((Ideal.quotientKerAlgEquivOfSurjective (f := (f : H →ₐ[K] H')) hf).symm : H' →ₐ[K] H ⧸ kerB f)
    (AlgHom.ext fun a => by
      change (Ideal.quotientKerAlgEquivOfSurjective hf).symm ((f : H →ₐ[K] H') a) = _
      rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]; rfl)

omit [CommRing R] in
theorem kerLiftBInv_apply (f : H →ₐc[K] H') (hf : Surjective f) (x : H) :
    kerLiftBInv f hf (f x) = Ideal.Quotient.mk (kerB f) x := by
  change (Ideal.quotientKerAlgEquivOfSurjective hf).symm ((f : H →ₐ[K] H') x) = _
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]

omit [CommRing R] in
theorem kerLiftB_kerLiftBInv (f : H →ₐc[K] H') (hf : Surjective f) (y : H') :
    kerLiftB f (kerLiftBInv f hf y) = y := by
  obtain ⟨x, rfl⟩ := hf y
  rw [kerLiftBInv_apply]; rfl

end BiIdealTools
p2m_reactivate "P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.HopfAlgebra.WittLevelInduction.Quot"

end Quot
p2m_reactivate "P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.HopfAlgebra.WittLevelInduction.Quot"

section Dual

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
variable (X : Type v) [CommRing X] [Bialgebra k X] [Module.Finite k X]

open CartierDual

def HV (m : ℕ) : Prop := ∀ φ : CartierDual k X, φ 1 = 0 → φ ^ p ^ m = 0

variable {k p X}

theorem toDual_pow (φ : CartierDual k X) (m : ℕ) :
    CartierDual.toDual k X (φ ^ m) = (WithConv.toConv (CartierDual.toDual k X φ) ^ m).ofConv := by
  induction m with
  | zero =>
    refine LinearMap.ext fun a => ?_
    rw [pow_zero, pow_zero, LinearMap.convOne_apply, Algebra.algebraMap_self_apply]
    exact CartierDual.one_apply a
  | succ m ih =>
    rw [pow_succ, CartierDual.toDual_mul, ih, WithConv.toConv_ofConv, ← pow_succ]

theorem convPow_ofConv (β : WithConv (X →ₗ[k] k)) (m : ℕ) :
    (β ^ m).ofConv = CartierDual.toDual k X ((CartierDual.ofDual k X β.ofConv) ^ m) := by
  rw [toDual_pow, CartierDual.toDual_ofDual, WithConv.toConv_ofConv]

theorem convPow_apply (β : WithConv (X →ₗ[k] k)) (m : ℕ) (x : X) :
    (β ^ m).ofConv x = ((CartierDual.ofDual k X β.ofConv) ^ m) x := by
  rw [convPow_ofConv]; rfl

theorem convPow_mul_convPow_apply (β γ : WithConv (X →ₗ[k] k)) (m : ℕ) (x : X) :
    (β ^ m * γ ^ m).ofConv x =
      ((CartierDual.ofDual k X β.ofConv) ^ m * (CartierDual.ofDual k X γ.ofConv) ^ m) x := by
  have : β ^ m * γ ^ m = WithConv.toConv (CartierDual.toDual k X
      ((CartierDual.ofDual k X β.ofConv) ^ m * (CartierDual.ofDual k X γ.ofConv) ^ m)) := by
    rw [CartierDual.toDual_mul, toDual_pow, toDual_pow, CartierDual.toDual_ofDual,
      CartierDual.toDual_ofDual, WithConv.toConv_ofConv, WithConv.toConv_ofConv,
      WithConv.toConv_ofConv]
  rw [this]; rfl

variable (k p X) in

theorem hV_iff (m : ℕ) :
    (∀ β : WithConv (X →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ m = 0) ↔ HV k p X m := by
  constructor
  · intro h φ hφ
    have h1 := h (WithConv.toConv (CartierDual.toDual k X φ)) hφ
    have h2 : CartierDual.toDual k X (φ ^ p ^ m) = 0 := by
      rw [toDual_pow, h1, WithConv.ofConv_zero]
    exact CartierDual.ext fun a => congrArg (fun ψ : Module.Dual k X => ψ a) h2
  · intro h β hβ
    have h1 : (CartierDual.ofDual k X β.ofConv) ^ p ^ m = 0 := h _ hβ
    apply WithConv.ofConv_injective
    rw [convPow_ofConv, h1, map_zero, WithConv.ofConv_zero]

theorem mul_apply_one (φ ψ : CartierDual k X) : (φ * ψ) 1 = φ 1 * ψ 1 := by
  rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.dualDistrib_apply]
  rfl

theorem pow_apply_one (φ : CartierDual k X) (m : ℕ) : (φ ^ m) 1 = (φ 1) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, CartierDual.one_apply, Bialgebra.counit_one]
  | succ m ih => rw [pow_succ, mul_apply_one, ih, pow_succ]

theorem smul_apply' (c : k) (φ : CartierDual k X) (x : X) : (c • φ) x = c * φ x := rfl

theorem add_apply' (φ ψ : CartierDual k X) (x : X) : (φ + ψ) x = φ x + ψ x := rfl

theorem sub_apply' (φ ψ : CartierDual k X) (x : X) : (φ - ψ) x = φ x - ψ x := rfl

theorem algebraMap_injective : Injective (algebraMap k (CartierDual k X)) := by
  intro r s h
  have := congrArg (fun φ : CartierDual k X => φ 1) h
  simpa only [CartierDual.algebraMap_apply, Bialgebra.counit_one, one_mul] using this

scoped instance instCharP : CharP (CartierDual k X) p :=
  charP_of_injective_algebraMap algebraMap_injective p

def ev11 : CartierDual k X ⊗[k] CartierDual k X →ₗ[k] k :=
  LinearMap.mul' k k ∘ₗ TensorProduct.map ((CartierDual.pairing k X).flip 1)
    ((CartierDual.pairing k X).flip 1)

@[scoped simp] theorem ev11_tmul (φ ψ : CartierDual k X) : ev11 (φ ⊗ₜ[k] ψ) = φ 1 * ψ 1 := rfl

theorem algebraMap_tensor_injective :
    Injective (algebraMap k (CartierDual k X ⊗[k] CartierDual k X)) := by
  intro r s h
  have key : ∀ r : k, ev11 (algebraMap k (CartierDual k X ⊗[k] CartierDual k X) r) = r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, map_smul, Algebra.TensorProduct.one_def, ev11_tmul,
      CartierDual.one_apply, Bialgebra.counit_one, mul_one, smul_eq_mul, mul_one]
  have := congrArg (ev11 (k := k) (X := X)) h
  rwa [key, key] at this

scoped instance instCharP_tensor : CharP (CartierDual k X ⊗[k] CartierDual k X) p :=
  charP_of_injective_algebraMap algebraMap_tensor_injective p

theorem HV.mono {m m' : ℕ} (h : HV k p X m) (hm : m ≤ m') : HV k p X m' := fun φ hφ => by
  rw [← Nat.add_sub_cancel' hm, pow_add, pow_mul, h φ hφ, zero_pow (pow_ne_zero _ hp.out.ne_zero)]

theorem HV.of_surjective {Y : Type w} [CommRing Y] [Bialgebra k Y] [Module.Finite k Y] {m : ℕ}
    (h : HV k p X m) (f : X →ₐc[k] Y) (hf : Surjective f) : HV k p Y m := by
  intro ψ hψ
  have hinj : Injective (CartierDual.map f) := by
    intro a b hab
    refine CartierDual.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hf y
    exact congrArg (fun χ : CartierDual k X => χ x) hab
  apply hinj
  rw [map_pow, map_zero]
  apply h
  rw [CartierDual.map_apply, map_one]
  exact hψ

theorem HV.sub_pow {m : ℕ} (h : HV k p X m) (φ : CartierDual k X) :
    (φ - algebraMap k _ (φ 1)) ^ p ^ m = 0 :=
  h _ (by rw [sub_apply', CartierDual.algebraMap_apply, Bialgebra.counit_one, one_mul, sub_self])

end Dual
p2m_reactivate "P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.HopfAlgebra.WittLevelInduction.Quot"

section VImage

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] (n : ℕ)
variable (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]

open CartierDual Coalgebra

def Sn : Submodule k (Module.Dual k A) :=
  Submodule.span k (Set.range fun φ : CartierDual k A => CartierDual.toDual k A (φ ^ p ^ n))

def IK : Ideal A where
  carrier := {a | ∀ φ : CartierDual k A, (φ ^ p ^ n) a = 0}
  zero_mem' φ := map_zero _
  add_mem' {a b} ha hb φ := by rw [map_add, ha φ, hb φ, add_zero]
  smul_mem' c a ha φ := by

    rw [smul_eq_mul, ← CartierDual.comul_pairing (φ ^ p ^ n) c a]
    have hcomul : Coalgebra.comul (R := k) (φ ^ p ^ n) = (Coalgebra.comul (R := k) φ) ^ p ^ n := by
      have := map_pow (Bialgebra.comulAlgHom k (CartierDual k A)) φ (p ^ n)
      simpa only [Bialgebra.comulAlgHom_apply] using this

    have hfd := sum_pow_char_pow p n (ℛ k φ).index (fun i => (ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i)
    have hfd' : (∑ i ∈ (ℛ k φ).index, (ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i) ^ p ^ n =
        ∑ i ∈ (ℛ k φ).index, ((ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i) ^ p ^ n := hfd
    rw [hcomul, ← (ℛ k φ).eq, hfd', map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have htp : ((ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i) ^ p ^ n =
        ((ℛ k φ).left i ^ p ^ n) ⊗ₜ[k] ((ℛ k φ).right i ^ p ^ n) :=
      Algebra.TensorProduct.tmul_pow _ _ _
    rw [htp, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]
    change ((ℛ k φ).left i ^ p ^ n) c * ((ℛ k φ).right i ^ p ^ n) a = 0
    rw [ha, mul_zero]

variable {k p n A}

theorem apply_eq_zero_of_mem_Sn {f : Module.Dual k A} (hf : f ∈ Sn k p n A) {a : A}
    (ha : a ∈ IK k p n A) : f a = 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, rfl⟩ := hx
    exact ha φ
  | zero => rfl
  | add x y _ _ hx hy => rw [LinearMap.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [LinearMap.smul_apply, hx, smul_zero]

theorem IK_eq_dualCoannihilator (a : A) :
    a ∈ IK k p n A ↔ a ∈ (Sn k p n A).dualCoannihilator := by
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro ha f hf
    exact apply_eq_zero_of_mem_Sn hf ha
  · intro h φ
    exact h _ (Submodule.subset_span ⟨φ, rfl⟩)

theorem mem_Sn_of_forall_apply_eq_zero (f : Module.Dual k A) (hf : ∀ a ∈ IK k p n A, f a = 0) :
    f ∈ Sn k p n A := by
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Sn k p n A),
    Submodule.mem_dualAnnihilator]
  intro a ha
  exact hf a ((IK_eq_dualCoannihilator a).2 ha)

theorem mul_mem_Sn {s t : CartierDual k A} (hs : CartierDual.toDual k A s ∈ Sn k p n A)
    (ht : CartierDual.toDual k A t ∈ Sn k p n A) :
    CartierDual.toDual k A (s * t) ∈ Sn k p n A := by

  have gen : ∀ φ ψ : CartierDual k A,
      CartierDual.toDual k A (φ ^ p ^ n * ψ ^ p ^ n) ∈ Sn k p n A := fun φ ψ => by
    rw [← mul_pow]
    exact Submodule.subset_span ⟨φ * ψ, rfl⟩

  have step1 : ∀ ψ : CartierDual k A, ∀ f ∈ Sn k p n A,
      CartierDual.toDual k A (CartierDual.ofDual k A f * ψ ^ p ^ n) ∈ Sn k p n A := by
    intro ψ f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, rfl⟩ := hx
      rw [CartierDual.ofDual_toDual]; exact gen φ ψ
    | zero => rw [map_zero, zero_mul, map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add, add_mul, map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul, smul_mul_assoc, map_smul]; exact Submodule.smul_mem _ c hx
  have step2 : ∀ f ∈ Sn k p n A,
      CartierDual.toDual k A (s * CartierDual.ofDual k A f) ∈ Sn k p n A := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ψ, rfl⟩ := hx
      rw [CartierDual.ofDual_toDual]
      have := step1 ψ _ hs
      rwa [CartierDual.ofDual_toDual] at this
    | zero => rw [map_zero, mul_zero, map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add, mul_add, map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul, mul_smul_comm, map_smul]; exact Submodule.smul_mem _ c hx
  have := step2 _ ht
  rwa [CartierDual.ofDual_toDual] at this

scoped instance isHopfIdeal_IK : IsHopfIdeal' k (IK k p n A) := by
  refine { map_mkₐ_comul_eq_zero := ?_, counit_eq_zero := ?_, antipode_mem := ?_ }
  · intro a ha
    set I := IK k p n A

    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro F
    obtain ⟨w, rfl⟩ := (TensorProduct.dualDistribEquiv k (A ⧸ I) (A ⧸ I)).surjective F
    change TensorProduct.dualDistrib k (A ⧸ I) (A ⧸ I) w _ = 0
    induction w with
    | zero => simp
    | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | tmul lam mu =>
      let mk : A →ₗ[k] A ⧸ I := (Ideal.Quotient.mkₐ k I).toLinearMap
      have hnat : ∀ z : A ⊗[k] A, TensorProduct.dualDistrib k (A ⧸ I) (A ⧸ I) (lam ⊗ₜ[k] mu)
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I) z) =
          TensorProduct.dualDistrib k A A ((lam ∘ₗ mk) ⊗ₜ[k] (mu ∘ₗ mk)) z := by
        intro z
        induction z with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y => rfl
      rw [hnat]

      have hl : lam ∘ₗ mk ∈ Sn k p n A := mem_Sn_of_forall_apply_eq_zero _ fun x hx => by
        change lam (Ideal.Quotient.mk I x) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
      have hm : mu ∘ₗ mk ∈ Sn k p n A := mem_Sn_of_forall_apply_eq_zero _ fun x hx => by
        change mu (Ideal.Quotient.mk I x) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
      have hprod := mul_mem_Sn (s := CartierDual.ofDual k A (lam ∘ₗ mk))
        (t := CartierDual.ofDual k A (mu ∘ₗ mk)) (by simpa using hl) (by simpa using hm)
      have := apply_eq_zero_of_mem_Sn hprod ha
      rw [CartierDual.toDual_apply, CartierDual.mul_apply] at this
      simpa only [CartierDual.toDual_ofDual] using this
  · intro a ha
    have := ha 1
    rwa [one_pow, CartierDual.one_apply] at this
  · intro a ha φ
    rw [← CartierDual.antipode_apply, show HopfAlgebra.antipode k (φ ^ p ^ n) =
      Quot.antipodeAlgHom' k (φ ^ p ^ n) from rfl, map_pow]
    exact ha _

abbrev μK : A →ₐc[k] A ⧸ IK k p n A := Quot.mkB k (IK k p n A)

theorem exists_factor (f : Module.Dual k A) (hf : ∀ a ∈ IK k p n A, f a = 0) :
    ∃ g : Module.Dual k (A ⧸ IK k p n A), f = g ∘ₗ (μK (k := k) (p := p) (n := n) (A := A)).toLinearMap := by
  set mk : A →ₗ[k] A ⧸ IK k p n A := (μK (k := k) (p := p) (n := n) (A := A)).toLinearMap
  have hsurj : Surjective mk := Ideal.Quotient.mk_surjective
  obtain ⟨σ, hσ⟩ := mk.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  refine ⟨f ∘ₗ σ, LinearMap.ext fun a => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have h1 : mk (σ (mk a)) = mk a := by
    have := LinearMap.congr_fun hσ (mk a); simpa using this
  have h2 : σ (mk a) - a ∈ IK k p n A := by
    have : mk (σ (mk a) - a) = 0 := by rw [map_sub, h1, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  have := hf _ h2
  rw [map_sub, sub_eq_zero] at this
  exact this.symm

theorem dualDistrib_comp_comp {P Q : Type*} [AddCommGroup P] [Module k P] [AddCommGroup Q]
    [Module k Q] (f g : Module.Dual k Q) (h : P →ₗ[k] Q) (z : P ⊗[k] P) :
    TensorProduct.dualDistrib k P P ((f ∘ₗ h) ⊗ₜ[k] (g ∘ₗ h)) z =
      TensorProduct.dualDistrib k Q Q (f ⊗ₜ[k] g) (TensorProduct.map h h z) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => rfl

theorem apply_eq_counit_mul_of_mem_hopfKer (s : CartierDual k A)
    (hs : CartierDual.toDual k A s ∈ Sn k p n A) {a : A}
    (ha : a ∈ HopfAlgebra.hopfKer (μK (k := k) (p := p) (n := n) (A := A))) :
    s a = Coalgebra.counit (R := k) a * s 1 := by
  obtain ⟨g, hg⟩ := exists_factor (CartierDual.toDual k A s)
    (fun x hx => apply_eq_zero_of_mem_Sn hs hx)
  have hco : Algebra.TensorProduct.map (AlgHom.id k A)
      ((μK (k := k) (p := p) (n := n) (A := A)) : A →ₐ[k] A ⧸ IK k p n A)
        (Coalgebra.comul (R := k) a) = a ⊗ₜ[k] 1 := ha
  have h1 : s a = (1 * s) a := by rw [one_mul]
  rw [h1, CartierDual.mul_apply]

  have hnat : ∀ z : A ⊗[k] A, TensorProduct.dualDistrib k A A
      (CartierDual.toDual k A 1 ⊗ₜ[k] CartierDual.toDual k A s) z =
      TensorProduct.dualDistrib k A (A ⧸ IK k p n A) (CartierDual.toDual k A 1 ⊗ₜ[k] g)
        (Algebra.TensorProduct.map (AlgHom.id k A)
          ((μK (k := k) (p := p) (n := n) (A := A)) : A →ₐ[k] A ⧸ IK k p n A) z) := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, TensorProduct.dualDistrib_apply,
        TensorProduct.dualDistrib_apply, hg]
      rfl
  rw [hnat, hco, TensorProduct.dualDistrib_apply, CartierDual.toDual_apply, CartierDual.one_apply]
  congr 1
  have := LinearMap.congr_fun hg 1
  rw [CartierDual.toDual_apply] at this
  rw [this]; rfl

section WithHV

variable (hV : HV k p A (n + 1))
include hV

theorem HV_one_quotient : HV k p (A ⧸ IK k p n A) 1 := by
  intro ψ hψ
  set μ : A →ₐc[k] A ⧸ IK k p n A := μK
  have hinj : Injective (CartierDual.map μ) := by
    intro a b hab
    refine CartierDual.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := IK k p n A) y
    exact congrArg (fun χ : CartierDual k A => χ x) hab
  set s : CartierDual k A := CartierDual.map μ ψ with hs_def
  have hs : CartierDual.toDual k A s ∈ Sn k p n A :=
    mem_Sn_of_forall_apply_eq_zero _ fun x hx => by
      change ψ (μ x) = 0
      rw [show μ x = 0 from Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

  have Q : ∀ f ∈ Sn k p n A,
      (CartierDual.ofDual k A f - algebraMap k _ (f 1)) ^ p = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, rfl⟩ := hx
      rw [CartierDual.ofDual_toDual, CartierDual.toDual_apply, pow_apply_one, map_pow,
        ← sub_pow_char_pow, ← pow_mul, ← pow_succ]
      exact hV.sub_pow φ
    | zero => rw [map_zero, LinearMap.zero_apply, map_zero, sub_zero, zero_pow hp.out.ne_zero]
    | add x y _ _ hx hy =>
      rw [map_add, LinearMap.add_apply, map_add, add_sub_add_comm, add_pow_char, hx, hy, add_zero]
    | smul c x _ hx =>
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, ← Algebra.smul_def, ← smul_sub,
        smul_pow, hx, smul_zero]
  have hQ := Q _ hs
  have hs1 : s 1 = 0 := by rw [hs_def, CartierDual.map_apply, map_one]; exact hψ
  rw [CartierDual.ofDual_toDual, CartierDual.toDual_apply, hs1, map_zero, sub_zero] at hQ
  apply hinj
  rw [map_pow, pow_one, map_zero]
  exact hQ

end WithHV
p2m_reactivate "P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.HopfAlgebra.WittLevelInduction.Quot"

theorem HV_hopfKer
    [Module.Flat k A] [Module.Flat k (A ⧸ IK k p n A)]
    [Module.Flat k ↥(HopfAlgebra.hopfKer (μK (k := k) (p := p) (n := n) (A := A)))] :
    HV k p ↥(HopfAlgebra.hopfKer (μK (k := k) (p := p) (n := n) (A := A))) n := by
  set μ : A →ₐc[k] A ⧸ IK k p n A := μK
  set A' := HopfAlgebra.hopfKer μ
  intro ψ hψ

  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (A'.val.toLinearMap)
    (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  let φ : CartierDual k A := CartierDual.ofDual k A (CartierDual.toDual k _ ψ ∘ₗ r)
  have hφval : ∀ a : ↥A', φ (a : A) = ψ a := fun a => by
    change ψ (r (A'.val.toLinearMap a)) = ψ a
    rw [← LinearMap.comp_apply, hr, LinearMap.id_apply]
  have hφ1 : φ 1 = 0 := by
    have := hφval 1
    rw [OneMemClass.coe_one] at this
    rw [this]; exact hψ
  have hmap : CartierDual.map (HopfAlgebra.hopfKerVal μ) φ = ψ :=
    CartierDual.ext fun a => hφval a
  rw [← hmap, ← map_pow]
  refine CartierDual.ext fun a => ?_
  rw [CartierDual.map_apply, HopfAlgebra.HopfKerHopf.hopfKerVal_apply]
  change (φ ^ p ^ n) (a : A) = 0
  rw [apply_eq_counit_mul_of_mem_hopfKer (φ ^ p ^ n) (Submodule.subset_span ⟨φ, rfl⟩) a.2,
    pow_apply_one, hφ1, zero_pow (pow_ne_zero _ hp.out.ne_zero), mul_zero]

theorem mul_apply_of_comul_mk_eq (a : A)
    (hprim : Coalgebra.comul (R := k) ((μK (k := k) (p := p) (n := n) (A := A)) a) =
      (μK (k := k) (p := p) (n := n) (A := A)) a ⊗ₜ[k] 1 +
        1 ⊗ₜ[k] (μK (k := k) (p := p) (n := n) (A := A)) a)
    (s t : CartierDual k A) (hs : CartierDual.toDual k A s ∈ Sn k p n A)
    (ht : CartierDual.toDual k A t ∈ Sn k p n A) :
    (s * t) a = s a * t 1 + s 1 * t a := by
  obtain ⟨g, hg⟩ := exists_factor (CartierDual.toDual k A s)
    (fun x hx => apply_eq_zero_of_mem_Sn hs hx)
  obtain ⟨h, hh⟩ := exists_factor (CartierDual.toDual k A t)
    (fun x hx => apply_eq_zero_of_mem_Sn ht hx)
  set mk : A →ₗ[k] A ⧸ IK k p n A := (μK (k := k) (p := p) (n := n) (A := A)).toLinearMap
  have hΔ : TensorProduct.map mk mk (Coalgebra.comul (R := k) a) =
      mk a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] mk a := hprim
  rw [CartierDual.mul_apply, hg, hh, dualDistrib_comp_comp, hΔ, map_add,
    TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply]
  have e1 : s a = g (mk a) := by
    have := LinearMap.congr_fun hg a; exact this
  have e2 : t a = h (mk a) := by
    have := LinearMap.congr_fun hh a; exact this
  have e3 : s 1 = g 1 := by
    have := LinearMap.congr_fun hg 1; rw [CartierDual.toDual_apply] at this
    rw [this, LinearMap.comp_apply]; rfl
  have e4 : t 1 = h 1 := by
    have := LinearMap.congr_fun hh 1; rw [CartierDual.toDual_apply] at this
    rw [this, LinearMap.comp_apply]; rfl
  rw [e1, e2, e3, e4]

end VImage
p2m_reactivate "P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.HopfAlgebra.WittLevelInduction.Quot"

section Witt

open Deformation Deformation.TruncWitt

variable {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]

theorem coeff_eq_zero_of_hV_one {C : Type*} [CommRing C] [Bialgebra k C]
    (hV : ∀ β : WithConv (C →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ 1 = 0) :
    ∀ (m : ℕ) (t : TruncatedWittVector p (m + 1) C), t ∈ wittHom k p (m + 1) C →
      ∀ i : Fin (m + 1), i ≠ Fin.last m → t.coeff i = 0 := by
  intro m
  induction m with
  | zero =>
    intro t _ i hi
    exact absurd (Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)) hi
  | succ m ih =>
    intro t ht i hi
    obtain ⟨t', ht'⟩ := Deformation.wittHomShift_surjective_of_forall_convPow_eq_zero k p C 1 hV
      (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) ⟨t, ht⟩
    have e : t = shift (t' : TruncatedWittVector p (m + 1) C) := by
      have := congrArg Subtype.val ht'; exact this.symm
    subst e
    refine Fin.cases ?_ (fun j hj => ?_) i hi
    · intro _; exact coeff_shift_zero _
    · rw [coeff_shift_succ]
      refine ih _ t'.2 j fun h => hj ?_
      rw [h, Fin.succ_last]

theorem convPow_pow_apply_coeff {A : Type*} [CommRing A] [Bialgebra k A] {n : ℕ}
    {x : TruncatedWittVector p n A} (hx : x ∈ wittHom k p n A)
    (i : ℕ) (hi : i < n) (β : WithConv (A →ₗ[k] k)) :
    (β ^ p ^ i).ofConv (x.coeff ⟨i, hi⟩) = (β.ofConv (x.coeff ⟨0, Nat.zero_lt_of_lt hi⟩)) ^ p ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, pow_mul,
      (Deformation.convPow_prime_apply_coeff_of_mem_wittHom k p A k (β ^ p ^ i) hx).2 i hi,
      ih (Nat.lt_of_succ_lt hi), ← pow_mul]

theorem mem_wittHom_of_map_mem {Y Z : Type*} [CommRing Y] [Bialgebra k Y] [CommRing Z]
    [Bialgebra k Z] (j : Y →ₐc[k] Z) (hj : Injective j) {m : ℕ} (x : TruncatedWittVector p m Y)
    (hx : TruncWitt.map ((j : Y →ₐ[k] Z)).toRingHom x ∈ wittHom k p m Z) :
    x ∈ wittHom k p m Y := by
  rw [mem_wittHom_iff] at hx ⊢
  have hinj : Injective (Algebra.TensorProduct.map (j : Y →ₐ[k] Z) (j : Y →ₐ[k] Z)).toRingHom :=
    map_injective_of_injective (j : Y →ₐ[k] Z) hj
  apply TruncWitt.map_injective hinj
  have hΔ : (Algebra.TensorProduct.map (j : Y →ₐ[k] Z) (j : Y →ₐ[k] Z)).toRingHom.comp
      (comulRingHom k Y) = (comulRingHom k Z).comp (j : Y →ₐ[k] Z).toRingHom := by
    refine RingHom.ext fun c => ?_
    exact AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom j) c
  have h₁ : (Algebra.TensorProduct.map (j : Y →ₐ[k] Z) (j : Y →ₐ[k] Z)).toRingHom.comp
      (Algebra.TensorProduct.includeLeft : Y →ₐ[k] Y ⊗[k] Y).toRingHom =
      (Algebra.TensorProduct.includeLeft : Z →ₐ[k] Z ⊗[k] Z).toRingHom.comp
        (j : Y →ₐ[k] Z).toRingHom := by
    refine RingHom.ext fun c => ?_; simp
  have h₂ : (Algebra.TensorProduct.map (j : Y →ₐ[k] Z) (j : Y →ₐ[k] Z)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : Y →ₐ[k] Y ⊗[k] Y).toRingHom =
      (Algebra.TensorProduct.includeRight : Z →ₐ[k] Z ⊗[k] Z).toRingHom.comp
        (j : Y →ₐ[k] Z).toRingHom := by
    refine RingHom.ext fun c => ?_; simp
  rw [map_add, map_map, map_map, map_map, hΔ, h₁, h₂, ← map_map, ← map_map, ← map_map]
  exact hx

theorem wittHomMap_comp {X Y Z : Type*} [CommRing X] [Bialgebra k X] [CommRing Y] [Bialgebra k Y]
    [CommRing Z] [Bialgebra k Z] (f : X →ₐc[k] Y) (g : Y →ₐc[k] Z) {m : ℕ}
    (x : wittHom k p m X) :
    wittHomMap p m (g.comp f) x = wittHomMap p m g (wittHomMap p m f x) :=
  Subtype.ext (by rw [coe_wittHomMap, coe_wittHomMap, coe_wittHomMap, map_map]; rfl)

theorem wittHomMap_congr {X Y : Type*} [CommRing X] [Bialgebra k X] [CommRing Y] [Bialgebra k Y]
    {f g : X →ₐc[k] Y} (h : ∀ a, f a = g a) {m : ℕ} (x : wittHom k p m X) :
    wittHomMap p m f x = wittHomMap p m g x :=
  Subtype.ext (map_congr fun i => h _)

theorem comul_eq_of_mem_primitives {A : Type*} [CommRing A] [HopfAlgebra k A] {a : A}
    (ha : a ∈ primitives k A) : Coalgebra.comul (R := k) a = a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] a := by
  have h : Coalgebra.comul (R := k) a - a ⊗ₜ[k] 1 - 1 ⊗ₜ[k] a = 0 := ha
  rwa [sub_sub, sub_eq_zero] at h

end Witt
p2m_reactivate "P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.HopfAlgebra.WittLevelInduction.Quot"

section Induction

open Deformation Deformation.TruncWitt

variable (k : Type u) [Field k] [PerfectField k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

def P (n : ℕ) : Prop :=
  ∀ (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (B : Type v) [CommRing B] [Bialgebra k B] (π : A →ₐc[k] B) (_hπ : Surjective π)
    (_hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ n = 0),
    Surjective (Deformation.wittHomMap p n π)

theorem P_one : P.{u, v} k p 1 := by
  intro A _ _ _ _ B _ _ π hπ hV y
  have fin1 : ∀ i : Fin (0 + 1), i = Fin.last 0 := fun i =>
    Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
  have hvac : ∀ i : Fin (0 + 1), i ≠ Fin.last 0 → (y : TruncatedWittVector p 1 B).coeff i = 0 :=
    fun i hi => absurd (fin1 i) hi
  have hb := (Deformation.mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero
    (y : TruncatedWittVector p 1 B) hvac).1 y.2
  have hV1 : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p = 0 := by
    simpa only [pow_one] using hV
  obtain ⟨a, ha, hπa⟩ :=
    HopfAlgebra.exists_mem_primitives_map_eq_of_surjective_of_forall_convPow_prime_eq_zero
      k p A B π hπ hV1 _ hb
  let X : TruncatedWittVector p 1 A := TruncatedWittVector.mk p fun _ => a
  have hvacX : ∀ i : Fin (0 + 1), i ≠ Fin.last 0 → X.coeff i = 0 :=
    fun i hi => absurd (fin1 i) hi
  have hX : X ∈ wittHom k p 1 A := by
    refine (Deformation.mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero X hvacX).2 ?_
    rw [TruncatedWittVector.coeff_mk]
    exact comul_eq_of_mem_primitives ha
  refine ⟨⟨X, hX⟩, Subtype.ext (TruncatedWittVector.ext fun i => ?_)⟩
  rw [coeff_wittHomMap]
  obtain rfl : i = Fin.last 0 := fin1 i
  change π (X.coeff (Fin.last 0)) = _
  rw [TruncatedWittVector.coeff_mk]
  exact hπa

set_option maxHeartbeats 8000000 in

theorem P_succ (n : ℕ) (hn : 1 ≤ n) (ih : P.{u, v} k p n) : P.{u, v} k p (n + 1) := by
  intro A _ _ _ _ B _ _ π hπ hVconv y
  have hV : HV k p A (n + 1) := (hV_iff k p A (n + 1)).1 hVconv

  set I : Ideal A := IK k p n A with hI_def
  set μ : A →ₐc[k] A ⧸ I := μK with hμ_def
  set J : Ideal A := kerB π ⊔ I with hJ_def
  have hIJ : I ≤ J := le_sup_right
  have hπJ : kerB π ≤ J := le_sup_left
  set ν : (A ⧸ I) →ₐc[k] A ⧸ J := Quot.factorB k I hIJ with hν_def
  have hνs : Surjective ν := Quot.factorB_surjective k I hIJ

  set ρ : B →ₐc[k] A ⧸ J := (Quot.factorB k (kerB π) hπJ).comp (kerLiftBInv π hπ) with hρ_def
  have hρπ : ∀ a, ρ (π a) = Ideal.Quotient.mk J a := fun a => by
    rw [hρ_def, BialgHom.comp_apply, kerLiftBInv_apply]; rfl
  have hρs : Surjective ρ := fun z => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨π a, hρπ a⟩

  have hV_K1 : HV k p (A ⧸ I) 1 := HV_one_quotient hV
  have hV_K1c := (hV_iff k p (A ⧸ I) 1).2 hV_K1
  have hV_Knc := (hV_iff k p (A ⧸ I) n).2 (hV_K1.mono hn)
  have hV_J1c := (hV_iff k p (A ⧸ J) 1).2 (hV_K1.of_surjective ν hνs)

  obtain ⟨t₀, ht₀⟩ := Deformation.wittHomShift_surjective_of_forall_convPow_eq_zero k p (A ⧸ J)
    1 hV_J1c n hn (wittHomMap p (n + 1) ρ y)
  obtain ⟨t₁, rfl⟩ := ih (A ⧸ I) (A ⧸ J) ν hνs hV_Knc t₀
  set t : wittHom k p (n + 1) (A ⧸ I) := wittHomShift k p n (A ⧸ I) t₁ with ht_def
  have hyt : wittHomMap p (n + 1) ρ y = wittHomMap p (n + 1) ν t := by
    rw [ht_def, wittHomMap_shift, ht₀]
  have ht_coeff : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      (t : TruncatedWittVector p (n + 1) (A ⧸ I)).coeff i = 0 :=
    coeff_eq_zero_of_hV_one hV_K1c n _ t.2
  set w₀ : A ⧸ I := (t : TruncatedWittVector p (n + 1) (A ⧸ I)).coeff (Fin.last n) with hw₀_def
  have hw₀ : Coalgebra.comul (R := k) w₀ = w₀ ⊗ₜ[k] 1 + 1 ⊗ₜ[k] w₀ :=
    (Deformation.mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero _ ht_coeff).1 t.2
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := I) w₀

  have hprim : Coalgebra.comul (R := k) (μ a) = μ a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] μ a := by
    change Coalgebra.comul (R := k) (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk I a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Ideal.Quotient.mk I a
    rw [ha]; exact hw₀
  have haUT : ∀ β γ : WithConv (A →ₗ[k] k),
      (β ^ p ^ n * γ ^ p ^ n).ofConv a =
        (β ^ p ^ n).ofConv a * (γ ^ p ^ n).ofConv 1 +
          (β ^ p ^ n).ofConv 1 * (γ ^ p ^ n).ofConv a := by
    intro β γ
    rw [convPow_mul_convPow_apply, convPow_apply, convPow_apply, convPow_apply, convPow_apply]
    exact mul_apply_of_comul_mk_eq a hprim _ _ (Submodule.subset_span ⟨_, rfl⟩)
      (Submodule.subset_span ⟨_, rfl⟩)
  obtain ⟨x₀, hx₀prim, hx₀⟩ :=
    HopfAlgebra.exists_mem_primitives_forall_apply_pow_eq_convPow_apply k p n A a haUT
  obtain ⟨X, hX, hX0⟩ :=
    (Deformation.exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero k p n A hVconv
      x₀).2 ⟨hx₀prim, a, hx₀⟩
  set x₁ : wittHom k p (n + 1) A := ⟨X, hX⟩ with hx₁_def
  have hx₁t : wittHomMap p (n + 1) μ x₁ = t := by
    refine Subtype.ext (TruncatedWittVector.ext fun i => ?_)
    by_cases hi : i = Fin.last n
    · subst hi
      rw [coeff_wittHomMap, ← hw₀_def, ← ha]
      change Ideal.Quotient.mk I (X.coeff (Fin.last n)) = Ideal.Quotient.mk I a
      refine (Ideal.Quotient.eq).2 fun φ => ?_
      rw [map_sub, sub_eq_zero]
      have h1 := convPow_pow_apply_coeff hX n (Nat.lt_succ_self n)
        (WithConv.toConv (CartierDual.toDual k A φ))
      have h2 := hx₀ (WithConv.toConv (CartierDual.toDual k A φ))
      rw [convPow_apply] at h1 h2
      simp only [CartierDual.ofDual_toDual, CartierDual.toDual_apply] at h1 h2
      have h0 : X.coeff ⟨0, Nat.zero_lt_of_lt (Nat.lt_succ_self n)⟩ = x₀ := hX0
      rw [h0, h2] at h1
      exact h1
    · rw [coeff_wittHomMap, ht_coeff i hi]
      have := coeff_eq_zero_of_hV_one hV_K1c n _ (wittHomMap p (n + 1) μ x₁).2 i hi
      rwa [coeff_wittHomMap] at this

  set y₂ : wittHom k p (n + 1) B := y - wittHomMap p (n + 1) π x₁ with hy₂_def
  have hy₂ : wittHomMap p (n + 1) ρ y₂ = 0 := by
    rw [hy₂_def, map_sub, hyt, ← hx₁t, ← wittHomMap_comp, ← wittHomMap_comp, sub_eq_zero]
    refine wittHomMap_congr (fun a' => ?_) _
    change ν (μ a') = ρ (π a')
    rw [hρπ]; rfl
  have hC1 := (Deformation.wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer ρ y₂).1 hy₂
  have hker : RingHom.ker (ρ : B →ₐ[k] A ⧸ J) =
      Ideal.map (π : A →ₐ[k] B) (RingHom.ker (μ : A →ₐ[k] A ⧸ I)) := by
    have hkμ : RingHom.ker (μ : A →ₐ[k] A ⧸ I) = I := Ideal.Quotient.mkₐ_ker k I
    rw [hkμ]
    apply le_antisymm
    · intro b hb
      obtain ⟨a', rfl⟩ := hπ b
      have hb' : ρ (π a') = 0 := hb
      rw [hρπ] at hb'
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (Ideal.Quotient.eq_zero_iff_mem.1 hb')
      rw [← huv, map_add, show ((π : A →ₐc[k] B) : A → B) u = (π : A →ₐ[k] B) u from rfl,
        (RingHom.mem_ker.1 hu : (π : A →ₐ[k] B) u = 0), zero_add]
      exact Ideal.mem_map_of_mem _ hv
    · rw [Ideal.map_le_iff_le_comap]
      intro v hv
      change ρ (π v) = 0
      rw [hρπ]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (hIJ hv)
  have hIM := HopfAlgebra.map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker k π μ ρ hπ
    (Quot.mkB_surjective k I) hρs hker
  have hcoef : ∀ i, ∃ c ∈ HopfAlgebra.hopfKer μ,
      π c = (y₂ : TruncatedWittVector p (n + 1) B).coeff i := fun i => by
    have := hC1 i
    rw [← hIM] at this
    exact Subalgebra.mem_map.1 this
  choose c hc hπc using hcoef

  let A' : Type v := ↥(HopfAlgebra.hopfKer μ)
  let val : A' →ₐc[k] A := HopfAlgebra.hopfKerVal μ
  let πA : A' →ₐc[k] B := π.comp val
  let q : A' →ₐc[k] A' ⧸ kerB πA := Quot.mkB k (kerB πA)
  have hqs : Surjective q := Quot.mkB_surjective k _
  let j : (A' ⧸ kerB πA) →ₐc[k] B := kerLiftB πA
  have hj : Injective j := kerLiftB_injective πA
  have hjq' : ∀ a' : A', j (q a') = πA a' := fun a' => rfl
  have hV_A' : HV k p A' n := HV_hopfKer
  have hV_A'c := (hV_iff k p A' n).2 hV_A'
  have hV_Bc := (hV_iff k p (A' ⧸ kerB πA) n).2 (hV_A'.of_surjective q hqs)

  let cw : TruncatedWittVector p (n + 1) A' := TruncatedWittVector.mk p fun i => ⟨c i, hc i⟩
  have hcw : TruncWitt.map ((πA : A' →ₐ[k] B)).toRingHom cw =
      (y₂ : TruncatedWittVector p (n + 1) B) :=
    TruncatedWittVector.ext fun i => by
      rw [coeff_map, TruncatedWittVector.coeff_mk]; exact hπc i
  have hjqR : ((πA : A' →ₐ[k] B)).toRingHom =
      ((j : (A' ⧸ kerB πA) →ₐ[k] B)).toRingHom.comp ((q : A' →ₐ[k] A' ⧸ kerB πA)).toRingHom :=
    RingHom.ext fun a' => (hjq' a').symm
  obtain ⟨yb, hyb_def⟩ : ∃ yb : TruncatedWittVector p (n + 1) (A' ⧸ kerB πA),
      yb = TruncWitt.map ((q : A' →ₐ[k] A' ⧸ kerB πA)).toRingHom cw := ⟨_, rfl⟩
  have hjyb : TruncWitt.map ((j : (A' ⧸ kerB πA) →ₐ[k] B)).toRingHom yb =
      (y₂ : TruncatedWittVector p (n + 1) B) := by
    rw [hyb_def, map_map, ← hjqR, hcw]
  have hyb2 : TruncWitt.map ((j : (A' ⧸ kerB πA) →ₐ[k] B)).toRingHom yb ∈
      wittHom k p (n + 1) B := by
    rw [hjyb]; exact y₂.2
  have hyb : yb ∈ wittHom k p (n + 1) (A' ⧸ kerB πA) := mem_wittHom_of_map_mem j hj yb hyb2

  obtain ⟨u, hu⟩ := Deformation.wittHomShift_surjective_of_forall_convPow_eq_zero k p
    (A' ⧸ kerB πA) n hV_Bc n le_rfl ⟨yb, hyb⟩
  obtain ⟨uu, huu⟩ := ih A' (A' ⧸ kerB πA) q hqs hV_A'c u

  refine ⟨x₁ + wittHomMap p (n + 1) val (wittHomShift k p n A' uu), ?_⟩
  have key : wittHomMap p (n + 1) π (wittHomMap p (n + 1) val (wittHomShift k p n A' uu)) = y₂ := by
    rw [← wittHomMap_comp]
    refine Subtype.ext ?_
    rw [coe_wittHomMap, coe_wittHomShift, ← hjyb]
    change TruncWitt.map ((πA : A' →ₐ[k] B)).toRingHom (shift (uu : TruncatedWittVector p n A')) = _
    rw [hjqR, ← map_map, map_shift]
    congr 1
    have h1 : TruncWitt.map ((q : A' →ₐ[k] A' ⧸ kerB πA)).toRingHom
        (uu : TruncatedWittVector p n A') = (u : TruncatedWittVector p n (A' ⧸ kerB πA)) := by
      have := congrArg Subtype.val huu; exact this
    have h2 : shift (u : TruncatedWittVector p n (A' ⧸ kerB πA)) = yb := by
      have := congrArg Subtype.val hu; exact this
    rw [h1, h2]
  rw [map_add, key, hy₂_def, add_sub_cancel]

theorem P_all (n : ℕ) (hn : 1 ≤ n) : P.{u, v} k p n := by
  induction n, hn using Nat.le_induction with
  | base => exact P_one k p
  | succ m hm ih => exact P_succ k p m hm ih

theorem wittHomMap_surjective (n : ℕ) [NeZero n]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (B : Type w) [CommRing B] [Bialgebra k B]
    (π : A →ₐc[k] B) (hπ : Surjective π)
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ n = 0) :
    Surjective (Deformation.wittHomMap p n π) := by
  have hn : 1 ≤ n := NeZero.one_le
  intro y
  obtain ⟨x, hx⟩ := P_all k p n hn A (A ⧸ kerB π) (Quot.mkB k (kerB π))
    (Quot.mkB_surjective k _) hV (wittHomMap p n (kerLiftBInv π hπ) y)
  refine ⟨x, ?_⟩
  have h1 : wittHomMap p n π x = wittHomMap p n ((kerLiftB π).comp (Quot.mkB k (kerB π))) x :=
    wittHomMap_congr (fun a => rfl) x
  rw [h1, wittHomMap_comp, hx, ← wittHomMap_comp]
  refine Subtype.ext ?_
  rw [coe_wittHomMap]
  conv_rhs => rw [← TruncWitt.map_id (y : TruncatedWittVector p n B)]
  refine map_congr fun i => ?_
  exact kerLiftB_kerLiftBInv π hπ _

end Induction
p2m_reactivate "P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.HopfAlgebra.WittLevelInduction.Quot"

end HopfAlgebra.WittLevelInduction
p2m_reactivate "P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.HopfAlgebra.WittLevelInduction.Quot P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.HopfAlgebra P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.HopfAlgebra.WittLevelInduction"
p2m_reactivate "P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.HopfAlgebra.WittLevelInduction.Quot P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.HopfAlgebra"

theorem solution
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) [NeZero n]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (B : Type w) [CommRing B] [Bialgebra k B]
    (π : A →ₐc[k] B) (hπ : Function.Surjective π)
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ n = 0) :
    Function.Surjective (Deformation.wittHomMap p n π) :=
  HopfAlgebra.WittLevelInduction.wittHomMap_surjective k p n A B π hπ hV

end
end S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero
end P2MW
export P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero (solution)

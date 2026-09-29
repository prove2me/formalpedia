-- Prove2me | solution 1 for HopfAlgebra.exists_quotientFlag_of_galoisStableChain_of_fixedPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/80154553-8f04-509a-92a2-11b1d0ecbd71

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints

open scoped TensorProduct

noncomputable section

namespace S17
namespace QuotientFlagGen

universe u v

section HopfQuot

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]

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

variable (R) in

structure IsHopfIdeal' (I : Ideal A) : Prop where
  counit_eq_zero : ∀ x ∈ I, Coalgebra.counit (R := R) x = 0
  map_comul_eq_zero : ∀ x ∈ I,
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) x) = 0
  antipode_mem : ∀ x ∈ I, HopfAlgebra.antipode R x ∈ I

def HQ (I : Ideal A) (_hI : IsHopfIdeal' R I) : Type v := A ⧸ I

variable (I : Ideal A) (hI : IsHopfIdeal' R I)

scoped instance HQ.instCommRing : CommRing (HQ I hI) := inferInstanceAs (CommRing (A ⧸ I))
p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"
scoped instance HQ.instAlgebra : Algebra R (HQ I hI) := inferInstanceAs (Algebra R (A ⧸ I))

p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"

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

p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"
theorem HQ.liftₐ_comp {B : Type*} [Semiring B] [Algebra R B] (f : A →ₐ[R] B)
    (hf : ∀ a ∈ I, f a = 0) : (HQ.liftₐ I hI f hf).comp (HQ.mkₐ I hI) = f :=
  AlgHom.ext fun _ => rfl

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

p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"
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

p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"

def HQ.mkB : A →ₐc[R] C :=
  BialgHom.ofAlgHom (HQ.mkₐ I hI) (HQ.counit_comp_mk I hI) (HQ.comul_comp_mk I hI).symm

@[scoped simp] theorem HQ.mkB_apply (x : A) : HQ.mkB I hI x = π x := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"
theorem HQ.mkB_toAlgHom : (HQ.mkB I hI : A →ₐ[R] C) = π := rfl

theorem HQ.mkB_surjective : Function.Surjective (HQ.mkB I hI) := HQ.mkₐ_surjective I hI

scoped instance HQ.instFiniteType [Algebra.FiniteType R A] : Algebra.FiniteType R C :=
  Algebra.FiniteType.of_surjective (HQ.mkₐ I hI) (HQ.mkₐ_surjective I hI)

p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"
scoped instance HQ.instModuleFinite [Module.Finite R A] : Module.Finite R C :=
  Module.Finite.of_surjective (π).toLinearMap (HQ.mkₐ_surjective I hI)

p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"

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

theorem HQ.exists_factor_iff {B : Type*} [Semiring B] [Algebra R B] (f : A →ₐ[R] B) :
    (∃ g : C →ₐ[R] B, g.comp (HQ.mkB I hI : A →ₐ[R] C) = f) ↔ ∀ a ∈ I, f a = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ a ha
    rw [AlgHom.comp_apply, HQ.mkB_toAlgHom, (HQ.mkₐ_eq_zero_iff I hI a).mpr ha, map_zero]
  · intro hf
    exact ⟨HQ.liftₐ I hI f hf, HQ.liftₐ_comp I hI f hf⟩

def HQ.factor (J : Ideal A) (hJ : IsHopfIdeal' R J) (hle : I ≤ J) : C →ₐc[R] HQ J hJ :=
  BialgHom.ofAlgHom
    (HQ.liftₐ I hI (HQ.mkₐ J hJ) fun a ha => (HQ.mkₐ_eq_zero_iff J hJ a).mpr (hle ha))
    (by
      refine HQ.algHom_ext I hI ?_
      rw [AlgHom.comp_assoc, HQ.liftₐ_comp, HQ.counitAlgHom_eq, HQ.counitAlgHom_eq,
        HQ.counit_comp_mk, HQ.counit_comp_mk])
    (by
      refine HQ.algHom_ext I hI ?_
      rw [AlgHom.comp_assoc, AlgHom.comp_assoc, HQ.liftₐ_comp, HQ.comulAlgHom_eq,
        HQ.comulAlgHom_eq, HQ.comul_comp_mk, HQ.comul_comp_mk, ← AlgHom.comp_assoc,
        ← Algebra.TensorProduct.map_comp, HQ.liftₐ_comp])

theorem HQ.factor_comp (J : Ideal A) (hJ : IsHopfIdeal' R J) (hle : I ≤ J) :
    (HQ.factor I hI J hJ hle).comp (HQ.mkB I hI) = HQ.mkB J hJ := by
  ext x; rfl

theorem HQ.factor_surjective (J : Ideal A) (hJ : IsHopfIdeal' R J) (hle : I ≤ J) :
    Function.Surjective (HQ.factor I hI J hJ hle) := by
  intro y
  obtain ⟨x, rfl⟩ := HQ.mkₐ_surjective J hJ y
  exact ⟨π x, rfl⟩

theorem isHopfIdeal_bot : IsHopfIdeal' R (⊥ : Ideal A) where
  counit_eq_zero x hx := by rw [(Submodule.mem_bot R).mp hx, map_zero]
  map_comul_eq_zero x hx := by rw [(Submodule.mem_bot R).mp hx, map_zero, map_zero]
  antipode_mem x hx := by rw [(Submodule.mem_bot R).mp hx, map_zero]; exact Submodule.zero_mem _

theorem HQ.mkB_bijective_of_bot (hI' : I = ⊥) : Function.Bijective (HQ.mkB I hI) := by
  refine ⟨fun x y hxy => ?_, HQ.mkB_surjective I hI⟩
  have : π (x - y) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hxy
  rw [HQ.mkₐ_eq_zero_iff, hI'] at this
  exact sub_eq_zero.mp ((Submodule.mem_bot R).mp this)

end HopfQuot
p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

section FieldLemmas

variable {R : Type} [CommRing R] [Algebra R L]

variable (R) in

def FixesR (σ : L ≃ₐ[K] L) : Prop := ∀ r : R, σ (algebraMap R L r) = algebraMap R L r

theorem FixesR.symm {σ : L ≃ₐ[K] L} (hσ : FixesR R σ) : FixesR R σ.symm := fun r => by
  conv_lhs => rw [← hσ r]
  exact σ.symm_apply_apply _

variable (K L R) in

abbrev FixedPointsInFrac : Prop :=
  ∀ c : L, (∀ σ : L ≃ₐ[K] L, FixesR R σ → σ c = c) →
    ∃ a b : R, algebraMap R L b ≠ 0 ∧ c * algebraMap R L b = algebraMap R L a

theorem fixed_mul_eq (hfix : FixedPointsInFrac K L R) (c : L) (hc : ∀ σ : L ≃ₐ[K] L, FixesR R σ → σ c = c) :
    ∃ a b : R, algebraMap R L b ≠ 0 ∧ c * algebraMap R L b = algebraMap R L a := hfix c hc

theorem descent_indep (hfp : FixedPointsInFrac K L R) {S ι : Type} [Fintype ι] [DecidableEq ι]
    (y : ι → S → L)
    (hy : ∀ σ : L ≃ₐ[K] L, FixesR R σ → ∀ s : S, ∃ t : S, ∀ i, y i s = σ (y i t))
    (hind : ∀ r : ι → R, (∀ s, ∑ i, algebraMap R L (r i) * y i s = 0) → ∀ i, r i = 0) :
    ∀ c : ι → L, (∀ s, ∑ i, c i * y i s = 0) → ∀ i, c i = 0 := by
  classical
  suffices h : ∀ (k : ℕ) (c : ι → L), (Finset.univ.filter fun i => c i ≠ 0).card ≤ k →
      (∀ s, ∑ i, c i * y i s = 0) → ∀ i, c i = 0 from
    fun c hc => h _ c le_rfl hc
  intro k
  induction k with
  | zero =>
    intro c hk hc i
    by_contra hi
    have hmem : i ∈ Finset.univ.filter fun i => c i ≠ 0 := by simp [hi]
    rw [Nat.le_zero, Finset.card_eq_zero] at hk
    simp [hk] at hmem
  | succ k ih =>
    intro c hk hc
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀⟩ := hne
    set c' : ι → L := fun i => c i / c i₀ with hc'
    have hc'i₀ : c' i₀ = 1 := div_self hi₀
    have hc'rel : ∀ s, ∑ i, c' i * y i s = 0 := by
      intro s
      simp only [hc', div_mul_eq_mul_div, ← Finset.sum_div, hc s, zero_div]
    have hsupp : ∀ i, c i = 0 → c' i = 0 := fun i h => by simp [hc', h]
    have hfix : ∀ σ : L ≃ₐ[K] L, FixesR R σ → ∀ i, σ (c' i) = c' i := by
      intro σ hσ
      set d : ι → L := fun i => σ (c' i) - c' i with hd
      have hd0 : ∀ i, d i = 0 := by
        refine ih d ?_ ?_
        · have hsub : (Finset.univ.filter fun i => d i ≠ 0) ⊆
              (Finset.univ.filter fun i => c i ≠ 0).erase i₀ := by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, ?_⟩
            · rintro rfl
              apply hi
              simp [hd, hc'i₀]
            · intro hci
              apply hi
              simp [hd, hsupp i hci]
          calc (Finset.univ.filter fun i => d i ≠ 0).card
              ≤ ((Finset.univ.filter fun i => c i ≠ 0).erase i₀).card := Finset.card_le_card hsub
            _ = (Finset.univ.filter fun i => c i ≠ 0).card - 1 :=
                Finset.card_erase_of_mem (by simp [hi₀])
            _ ≤ k := by omega
        · intro s
          obtain ⟨t, ht⟩ := hy σ hσ s
          simp only [hd, sub_mul, Finset.sum_sub_distrib, hc'rel s, sub_zero]
          calc ∑ i, σ (c' i) * y i s = ∑ i, σ (c' i * y i t) := by simp [ht, map_mul]
            _ = σ (∑ i, c' i * y i t) := by rw [map_sum]
            _ = 0 := by rw [hc'rel t, map_zero]
      intro i
      exact sub_eq_zero.mp (hd0 i)
    choose a b hb hab using fun i => fixed_mul_eq hfp (c' i) (fun σ hσ => hfix σ hσ i)
    set B : L := ∏ j, algebraMap R L (b j) with hBdef
    have hB : B ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hb j
    let r : ι → R := fun i => a i * ∏ j ∈ Finset.univ.erase i, b j
    have hr : ∀ i, algebraMap R L (r i) = c' i * B := by
      intro i
      simp only [r, hBdef, map_mul, map_prod]
      rw [← Finset.mul_prod_erase Finset.univ (fun j => algebraMap R L (b j)) (Finset.mem_univ i),
        ← hab i]
      ring
    have hrel : ∀ s, ∑ i, algebraMap R L (r i) * y i s = 0 := by
      intro s
      simp only [hr, mul_right_comm _ B, ← Finset.sum_mul, hc'rel s, zero_mul]
    have h0 := hind r hrel i₀
    have h1 : algebraMap R L (r i₀) = B := by rw [hr, hc'i₀, one_mul]
    rw [h0, map_zero] at h1
    exact hB h1.symm

end FieldLemmas
p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"

section TensorBasis

variable {R : Type*} [CommRing R] {P Q₀ : Type*} [AddCommGroup P] [Module R P]
  [AddCommGroup Q₀] [Module R Q₀] {ι : Type*}

def tcoeff (b : Module.Basis ι R Q₀) (j : ι) : P ⊗[R] Q₀ →ₗ[R] P :=
  (TensorProduct.rid R P).toLinearMap ∘ₗ (b.coord j).lTensor P

theorem tcoeff_tmul (b : Module.Basis ι R Q₀) (j : ι) (p : P) (q : Q₀) :
    tcoeff b j (p ⊗ₜ[R] q) = (b.repr q j) • p := by
  simp [tcoeff]

theorem sum_tcoeff_tmul [Fintype ι] (b : Module.Basis ι R Q₀) (z : P ⊗[R] Q₀) :
    ∑ j, tcoeff b j z ⊗ₜ[R] b j = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    simp_rw [tcoeff_tmul, TensorProduct.smul_tmul, ← TensorProduct.tmul_sum]
    rw [b.sum_repr q]
  | add x y hx hy =>
    simp_rw [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]

end TensorBasis
p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"

section TensorTest

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Algebra R L]

theorem tensor_test
    {P Q : Type} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.IsTorsionFree R Q]
    {S : Type} (φ : S → Q →ₗ[R] L)
    (hdesc : ∀ (ι : Type) [Fintype ι] (q : ι → Q), LinearIndependent R q →
      ∀ c : ι → L, (∀ s, ∑ i, c i * φ s (q i) = 0) → ∀ i, c i = 0)
    {T : Type} (t : T → P →ₗ[R] L) (ht : ∀ p : P, (∀ k, t k p = 0) → p = 0)
    (w : P ⊗[R] Q)
    (hw : ∀ k s, TensorProduct.lift ((LinearMap.mul R L).compl₁₂ (t k) (φ s)) w = 0) :
    w = 0 := by
  classical
  obtain ⟨F, rfl⟩ := TensorProduct.exists_finset w
  let Q₀ : Submodule R Q := Submodule.span R ((F.image Prod.snd : Finset Q) : Set Q)
  haveI : Module.Finite R Q₀ := Module.Finite.span_of_finite R (Finset.finite_toSet _)
  haveI : Module.IsTorsionFree R Q₀ :=
    Function.Injective.moduleIsTorsionFree Q₀.subtype Subtype.val_injective (fun _ _ => rfl)
  haveI : Module.Free R Q₀ := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R Q₀
  have hmem : ∀ x ∈ F, x.2 ∈ Q₀ := fun x hx =>
    Submodule.subset_span (by simpa using Finset.mem_image_of_mem Prod.snd hx)
  let w₀ : P ⊗[R] Q₀ := ∑ x ∈ F.attach, x.1.1 ⊗ₜ[R] (⟨x.1.2, hmem x.1 x.2⟩ : Q₀)
  have hw₀ : (Q₀.subtype).lTensor P w₀ = ∑ x ∈ F, x.1 ⊗ₜ[R] x.2 := by
    simp only [w₀, map_sum, LinearMap.lTensor_tmul, Submodule.subtype_apply]
    exact Finset.sum_attach F (fun x => x.1 ⊗ₜ[R] x.2)
  have hli : LinearIndependent R (fun j => (b j : Q)) :=
    b.linearIndependent.map' Q₀.subtype (Submodule.ker_subtype _)
  have hcoef : ∀ j, tcoeff b j w₀ = 0 := by
    intro j
    apply ht
    intro k
    refine hdesc _ (fun j => (b j : Q)) hli (fun j => t k (tcoeff b j w₀)) ?_ j
    intro s
    have h := hw k s
    rw [← hw₀, ← sum_tcoeff_tmul b w₀, map_sum, map_sum] at h
    simpa [LinearMap.lTensor_tmul, TensorProduct.lift.tmul] using h
  rw [← hw₀, ← sum_tcoeff_tmul b w₀]
  simp [hcoef]

end TensorTest
p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"

section Dedekind

variable {R : Type} [CommRing R] [Algebra R L]
variable {Q : Type} [AddCommGroup Q] [Module R Q]

def PhiL {S : Type} (φ : S → Q →ₗ[R] L) : L ⊗[R] Q →ₗ[L] (S → L) :=
  LinearMap.pi fun s => (Algebra.TensorProduct.lmul'' (S := L) R).toLinearMap ∘ₗ (φ s).baseChange L

@[scoped simp] theorem PhiL_tmul {S : Type} (φ : S → Q →ₗ[R] L) (a : L) (q : Q) (s : S) :
    PhiL φ (a ⊗ₜ[R] q) s = a * φ s q := by
  change Algebra.TensorProduct.lmul'' (S := L) R ((φ s).baseChange L (a ⊗ₜ[R] q)) = _
  rw [LinearMap.baseChange_tmul]
  rfl

theorem PhiL_apply_eq_lift {S : Type} (φ : S → Q →ₗ[R] L) (s : S) (w : L ⊗[R] Q) :
    PhiL φ w s = TensorProduct.lift ((LinearMap.mul R L).compl₁₂ LinearMap.id (φ s)) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a q => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end Dedekind
p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"

section DedekindAlg

variable {R : Type} [CommRing R] [Algebra R L]
variable {Q : Type} [CommRing Q] [Algebra R Q]

theorem PhiL_surjective {S : Type} [Fintype S] (g : S → (Q →ₐ[R] L))
    (hg : Function.Injective g) :
    Function.Surjective (PhiL fun s => (g s).toLinearMap) := by
  classical
  set Φ := PhiL fun s => (g s).toLinearMap with hΦ
  by_contra hsurj
  have hlt : LinearMap.range Φ < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hsurj (LinearMap.range_eq_top.mp h)
  obtain ⟨lam, hlam0, hlam⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  have hvan : ∀ q : Q, lam (fun s => g s q) = 0 := by
    intro q
    have h2 := hlam (LinearMap.mem_range_self Φ ((1 : L) ⊗ₜ[R] q))
    rw [LinearMap.mem_ker] at h2
    convert h2 using 2
    ext s
    simp [hΦ]
  have hexp : ∀ v : S → L, lam v = ∑ s, v s * lam (Pi.single s 1) := by
    intro v
    conv_lhs => rw [show v = ∑ s, v s • (Pi.single s (1 : L) : S → L) from by
      ext i; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, map_smul, smul_eq_mul]
  have hinj : Function.Injective fun s => (g s : Q →* L) := by
    intro s t hst
    apply hg
    exact AlgHom.ext fun q => DFunLike.congr_fun hst q
  have hind := (linearIndependent_monoidHom Q L).comp _ hinj
  have hrel : ∑ s, lam (Pi.single s 1) • (fun q => g s q : Q → L) = 0 := by
    ext q
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hvan q, hexp]
    simp [mul_comm]
  have hcoef := Fintype.linearIndependent_iff.mp hind (fun s => lam (Pi.single s 1)) hrel
  apply hlam0
  apply LinearMap.ext
  intro v
  rw [hexp]
  simp [hcoef]

end DedekindAlg
p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"

section Points

variable {R : Type} [CommRing R] [Algebra R L]
variable {H : Type} [CommRing H] [Algebra R H]

def galTwist (σ : L ≃ₐ[K] L) (hσ : FixesR R σ) (g : H →ₐ[R] L) : H →ₐ[R] L :=
  { (σ : L →+* L).comp (g : H →+* L) with
    commutes' := fun r => by simp [hσ r] }

@[scoped simp] theorem galTwist_apply (σ : L ≃ₐ[K] L) (hσ : FixesR R σ) (g : H →ₐ[R] L) (x : H) :
    galTwist σ hσ g x = σ (g x) := rfl

def J (S : Set (H →ₐ[R] L)) : Ideal H := ⨅ g : S, RingHom.ker (g : H →ₐ[R] L)

theorem mem_J {S : Set (H →ₐ[R] L)} {x : H} : x ∈ J S ↔ ∀ g ∈ S, g x = 0 := by
  simp only [J, Ideal.mem_iInf, RingHom.mem_ker, Subtype.forall]

theorem J_antitone {S T : Set (H →ₐ[R] L)} (h : S ⊆ T) : J T ≤ J S := fun _ hx =>
  mem_J.mpr fun g hg => mem_J.mp hx g (h hg)

def pbar (S : Set (H →ₐ[R] L)) (g : S) : (H ⧸ J S) →ₐ[R] L :=
  Ideal.Quotient.liftₐ (J S) (g : H →ₐ[R] L) (fun _ hx => (mem_J.mp hx) g g.2)

@[scoped simp] theorem pbar_mk (S : Set (H →ₐ[R] L)) (g : S) (x : H) :
    pbar S g (Ideal.Quotient.mk (J S) x) = (g : H →ₐ[R] L) x := rfl

theorem pbar_comp_mkₐ (S : Set (H →ₐ[R] L)) (g : S) :
    (pbar S g).comp (Ideal.Quotient.mkₐ R (J S)) = g :=
  AlgHom.ext fun _ => rfl

theorem pbar_injective (S : Set (H →ₐ[R] L)) : Function.Injective (pbar S) := by
  intro g h hgh
  apply Subtype.ext
  rw [← pbar_comp_mkₐ S g, ← pbar_comp_mkₐ S h, hgh]

theorem pbar_jointly_injective (S : Set (H →ₐ[R] L)) (q : H ⧸ J S)
    (hq : ∀ g : S, pbar S g q = 0) : q = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (mem_J.mpr fun g hg => hq ⟨g, hg⟩)

abbrev pfam (S : Set (H →ₐ[R] L)) : S → (H ⧸ J S) →ₗ[R] L := fun g => (pbar S g).toLinearMap

theorem isTorsionFree_quot [IsDomain R] (hR : Function.Injective (algebraMap R L))
    (S : Set (H →ₐ[R] L)) : Module.IsTorsionFree R (H ⧸ J S) := by
  haveI : Module.IsTorsionFree R L := Module.isTorsionFree_iff_algebraMap_injective.mpr hR
  refine Function.Injective.moduleIsTorsionFree (N := S → L) (fun q g => pbar S g q) ?_ ?_
  · intro q q' h
    rw [← sub_eq_zero]
    apply pbar_jointly_injective
    intro g
    have h' := congr_fun h g
    simp only at h'
    rw [map_sub, h', sub_self]
  · intro r q
    ext g
    simp

variable (K) in

def GalStable (S : Set (H →ₐ[R] L)) : Prop :=
  ∀ (σ : L ≃ₐ[K] L) (hσ : FixesR R σ), ∀ g ∈ S, galTwist σ hσ g ∈ S

theorem desc_quot (hfix : FixedPointsInFrac K L R) (S : Set (H →ₐ[R] L)) (hS : GalStable K S) (ι : Type) [Fintype ι]
    (q : ι → H ⧸ J S) (hq : LinearIndependent R q) (c : ι → L)
    (hc : ∀ g : S, ∑ i, c i * pfam S g (q i) = 0) : ∀ i, c i = 0 := by
  classical
  refine descent_indep (R := R) hfix (fun i (g : S) => pfam S g (q i)) ?_ ?_ c hc
  · intro σ hσ g
    refine ⟨⟨galTwist σ.symm hσ.symm g, hS _ _ g g.2⟩, fun i => ?_⟩
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (q i)
    show pfam S g (q i) = σ (pfam S ⟨galTwist σ.symm hσ.symm g, hS _ _ g g.2⟩ (q i))
    rw [← hx]
    simp
  · intro r hr
    have h0 : ∑ i, r i • q i = 0 := by
      apply pbar_jointly_injective
      intro g
      rw [map_sum]
      simpa [Algebra.smul_def] using hr g
    exact Fintype.linearIndependent_iff.mp hq r h0

theorem PhiL_pfam_injective [IsDomain R] [IsPrincipalIdealRing R] (hfix : FixedPointsInFrac K L R)
    (hR : Function.Injective (algebraMap R L))
    (S : Set (H →ₐ[R] L)) (hS : GalStable K S) : Function.Injective (PhiL (pfam S)) := by
  haveI := isTorsionFree_quot hR S
  rw [injective_iff_map_eq_zero]
  intro w hw
  refine tensor_test (pfam S) (desc_quot hfix S hS) (T := Unit) (fun _ => LinearMap.id)
    (fun p hp => hp ()) w ?_
  intro _ g
  rw [← PhiL_apply_eq_lift, hw]
  rfl

theorem mem_of_vanish [IsDomain R] [IsPrincipalIdealRing R] (hfix : FixedPointsInFrac K L R)
    (hR : Function.Injective (algebraMap R L)) [Finite (H →ₐ[R] L)]
    (S : Set (H →ₐ[R] L)) (hS : GalStable K S)
    (f : H →ₐ[R] L) (hf : ∀ x ∈ J S, f x = 0) : f ∈ S := by
  classical
  by_contra hfS
  haveI : Fintype S := Fintype.ofFinite S
  let fbar : (H ⧸ J S) →ₐ[R] L := Ideal.Quotient.liftₐ (J S) f hf
  have hfbar : ∀ g : S, fbar ≠ pbar S g := by
    intro g h
    apply hfS
    have hfg : f = g := by
      apply AlgHom.ext
      intro x
      exact DFunLike.congr_fun h (Ideal.Quotient.mk (J S) x)
    rw [hfg]
    exact g.2
  let g' : Option S → ((H ⧸ J S) →ₐ[R] L) := fun o => o.elim fbar (pbar S)
  have hg' : Function.Injective g' := by
    intro o₁ o₂ h
    cases o₁ with
    | none =>
      cases o₂ with
      | none => rfl
      | some g => exact absurd h (hfbar g)
    | some g =>
      cases o₂ with
      | none => exact absurd h.symm (hfbar g)
      | some g₂ => exact congrArg some (pbar_injective S h)
  have hsurj := PhiL_surjective g' hg'
  have hinj := PhiL_pfam_injective hfix hR S hS
  haveI : Module.Finite L (L ⊗[R] (H ⧸ J S)) := Module.Finite.of_injective _ hinj
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := LinearMap.finrank_range_le (PhiL fun o => (g' o).toLinearMap)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h2
  rw [Module.finrank_fintype_fun_eq_card] at h1 h2
  rw [Fintype.card_option] at h2
  omega

theorem finrank_quot [IsDomain R] [IsPrincipalIdealRing R] (hfix : FixedPointsInFrac K L R)
    (hR : Function.Injective (algebraMap R L)) [Module.Finite R H]
    (S : Set (H →ₐ[R] L)) [Fintype S] (hS : GalStable K S) :
    Module.finrank R (H ⧸ J S) = Fintype.card S := by
  haveI := isTorsionFree_quot hR S
  haveI : Module.Free R (H ⧸ J S) := Module.free_of_finite_type_torsion_free'
  have hbij : Function.Bijective (PhiL (pfam S)) :=
    ⟨PhiL_pfam_injective hfix hR S hS, PhiL_surjective (pbar S) (pbar_injective S)⟩
  have hL := (LinearEquiv.ofBijective _ hbij).finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card] at hL
  exact hL

end Points
p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"

section HopfPoints

variable {R : Type} [CommRing R] [Algebra R L]
variable {H : Type} [CommRing H] [HopfAlgebra R H]

theorem lift_comp_antipode_apply (g : H →ₐ[R] L) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift g (g.comp (antipodeAlgHom R H)) (fun _ _ => .all _ _) z
      = g (LinearMap.mul' R H ((HopfAlgebra.antipode R (A := H)).lTensor H z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, antipodeAlgHom_apply,
      LinearMap.lTensor_tmul, LinearMap.mul'_apply, map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem convMul_comp_antipode (g : H →ₐ[R] L) :
    WithConv.toConv g * WithConv.toConv (g.comp (antipodeAlgHom R H)) = 1 := by
  ext x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  rw [lift_comp_antipode_apply, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]

theorem convMul_toConv_apply (g h : H →ₐ[R] L) (x : H) :
    (WithConv.toConv g * WithConv.toConv h) x
      = Algebra.TensorProduct.lift g h (fun _ _ => .all _ _) (Coalgebra.comul (R := R) x) := by
  rw [AlgHom.convMul_apply]

theorem lift_pfam_map (S : Set (H →ₐ[R] L)) (k g : S) (z : H ⊗[R] H) :
    TensorProduct.lift ((LinearMap.mul R L).compl₁₂ (pfam S k) (pfam S g))
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (J S)) (Ideal.Quotient.mkₐ R (J S)) z)
      = Algebra.TensorProduct.lift (k : H →ₐ[R] L) (g : H →ₐ[R] L) (fun _ _ => .all _ _) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply,
      Algebra.TensorProduct.lift_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isHopfIdeal_J [IsDomain R] [IsPrincipalIdealRing R] (hfix : FixedPointsInFrac K L R)
    (hR : Function.Injective (algebraMap R L)) (S : Set (H →ₐ[R] L))
    (hS1 : (1 : WithConv (H →ₐ[R] L)).ofConv ∈ S)
    (hSmul : ∀ g ∈ S, ∀ h ∈ S, (WithConv.toConv g * WithConv.toConv h).ofConv ∈ S)
    (hSinv : ∀ g ∈ S, g.comp (antipodeAlgHom R H) ∈ S)
    (hSgal : GalStable K S) : IsHopfIdeal' R (J S) where
  counit_eq_zero x hx := by
    apply hR
    rw [map_zero, ← AlgHom.convOne_apply (R := R) (A := L) x]
    exact mem_J.mp hx _ hS1
  antipode_mem x hx := by
    rw [mem_J] at hx ⊢
    intro g hg
    exact hx _ (hSinv g hg)
  map_comul_eq_zero x hx := by
    haveI := isTorsionFree_quot hR S
    refine tensor_test (pfam S) (desc_quot hfix S hSgal) (pfam S) (pbar_jointly_injective S) _ ?_
    intro k g
    rw [lift_pfam_map, ← convMul_toConv_apply]
    exact mem_J.mp hx _ (hSmul k k.2 g g.2)

theorem HQ.flat_of_eq_J [IsDomain R] [IsPrincipalIdealRing R]
    (hR : Function.Injective (algebraMap R L)) (S : Set (H →ₐ[R] L))
    (I : Ideal H) (hI : IsHopfIdeal' R I) (h : I = J S) : Module.Flat R (HQ I hI) := by
  subst h
  haveI := isTorsionFree_quot hR S
  exact inferInstanceAs (Module.Flat R (H ⧸ J S))

omit [Algebra R L] in
theorem HQ.flat_of_eq_bot [Module.Flat R H]
    (I : Ideal H) (hI : IsHopfIdeal' R I) (h : I = ⊥) : Module.Flat R (HQ I hI) := by
  have hflat : Module.Flat R (H ⧸ I) :=
    Module.Flat.of_linearEquiv ((Submodule.quotEquivOfEqBot I h).restrictScalars R)
  exact hflat

theorem HQ.finrank_of_eq_J [IsDomain R] [IsPrincipalIdealRing R] (hfix : FixedPointsInFrac K L R)
    (hR : Function.Injective (algebraMap R L)) [Module.Finite R H]
    (S : Set (H →ₐ[R] L)) [Fintype S] (hS : GalStable K S)
    (I : Ideal H) (hI : IsHopfIdeal' R I) (h : I = J S) :
    Module.finrank R (HQ I hI) = Fintype.card S := by
  subst h
  exact finrank_quot hfix hR S hS

end HopfPoints
p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"

section Main

theorem main
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Algebra R L]
    (hR : Function.Injective (algebraMap R L))
    (hfix : FixedPointsInFrac K L R)
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    (M : Type) [AddCommGroup M] [Finite M]
    (e : WithConv (H →ₐ[R] L) ≃ M)
    (he : ∀ f g, e (f * g) = e f + e g)
    (act : (L ≃ₐ[K] L) → M → M)
    (hact : ∀ (σ : L ≃ₐ[K] L) (f g : WithConv (H →ₐ[R] L)),
        (∀ h : H, g h = σ (f h)) → e g = act σ (e f))
    (n : ℕ) (N : Fin (n + 1) → AddSubgroup M)
    (hmono : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (htop : N (Fin.last n) = ⊤)
    (hstab : ∀ (i : Fin (n + 1)) (σ : L ≃ₐ[K] L) (x : M), x ∈ N i → act σ x ∈ N i) :
    ∃ (B : Fin (n + 1) → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, HopfAlgebra R (B i))
      (π : ∀ i, H →ₐc[R] B i) (φ : ∀ i : Fin n, B i.succ →ₐc[R] B i.castSucc),
      (∀ i, Algebra.FiniteType R (B i)) ∧ (∀ i, Module.Flat R (B i)) ∧
      (∀ i, Function.Surjective (π i)) ∧ (∀ i, Function.Surjective (φ i)) ∧
      (∀ i : Fin n, (φ i).comp (π i.succ) = π i.castSucc) ∧
      Function.Bijective (π (Fin.last n)) ∧
      (∀ (i : Fin (n + 1)) (f : H →ₐ[R] L),
        (∃ g : B i →ₐ[R] L, g.comp (π i : H →ₐ[R] B i) = f) ↔
          e (WithConv.toConv f) ∈ N i) ∧
      (Coalgebra.IsCocomm R H → ∀ i, Coalgebra.IsCocomm R (B i)) ∧
      (Module.Finite R H → ∀ i, Module.Finite R (B i) ∧
        (i ≠ Fin.last n → Module.finrank R (B i) = Nat.card (N i))) := by
  classical

  haveI : Finite (WithConv (H →ₐ[R] L)) := Finite.of_equiv M e.symm
  haveI : Finite (H →ₐ[R] L) :=
    Finite.of_equiv (WithConv (H →ₐ[R] L)) (WithConv.equiv (H →ₐ[R] L))

  have he1 : e 1 = 0 := by
    have h := he 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h

  let S : Fin (n + 1) → Set (H →ₐ[R] L) := fun i => {g | e (WithConv.toConv g) ∈ N i}
  have hS1 : ∀ i, (1 : WithConv (H →ₐ[R] L)).ofConv ∈ S i := fun i => by
    show e (WithConv.toConv (WithConv.ofConv 1)) ∈ N i
    rw [WithConv.toConv_ofConv, he1]
    exact zero_mem _
  have hSmul : ∀ i, ∀ g ∈ S i, ∀ h ∈ S i,
      (WithConv.toConv g * WithConv.toConv h).ofConv ∈ S i := by
    intro i g hg h hh
    show e (WithConv.toConv (WithConv.ofConv _)) ∈ N i
    rw [WithConv.toConv_ofConv, he]
    exact add_mem hg hh
  have hSinv : ∀ i, ∀ g ∈ S i, g.comp (antipodeAlgHom R H) ∈ S i := by
    intro i g hg
    show e _ ∈ N i
    have h := he (WithConv.toConv g) (WithConv.toConv (g.comp (antipodeAlgHom R H)))
    rw [convMul_comp_antipode, he1] at h
    rw [eq_neg_of_add_eq_zero_right h.symm]
    exact neg_mem hg
  have hSgal : ∀ i, GalStable K (S i) := by
    intro i σ hσ g hg
    show e _ ∈ N i
    rw [hact σ (WithConv.toConv g) (WithConv.toConv (galTwist σ hσ g)) (fun h => rfl)]
    exact hstab i σ _ hg

  let I : Fin (n + 1) → Ideal H := fun i => if i = Fin.last n then ⊥ else J (S i)
  have hIJ : ∀ i, i ≠ Fin.last n → I i = J (S i) := fun i hi => if_neg hi
  have hIlast : I (Fin.last n) = ⊥ := if_pos rfl
  have hI : ∀ i, IsHopfIdeal' R (I i) := by
    intro i
    by_cases hi : i = Fin.last n
    · rw [hi, hIlast]; exact isHopfIdeal_bot
    · rw [hIJ i hi]; exact isHopfIdeal_J hfix hR (S i) (hS1 i) (hSmul i) (hSinv i) (hSgal i)
  have hle : ∀ i : Fin n, I i.succ ≤ I i.castSucc := by
    intro i
    by_cases hi : i.succ = Fin.last n
    · rw [show I i.succ = ⊥ from if_pos hi]; exact bot_le
    · rw [hIJ _ hi, hIJ _ (Fin.castSucc_lt_last i).ne]
      exact J_antitone (fun g hg => hmono i hg)
  refine ⟨fun i => HQ (I i) (hI i), fun i => inferInstance, fun i => inferInstance,
    fun i => HQ.mkB (I i) (hI i),
    fun i => HQ.factor (I i.succ) (hI i.succ) (I i.castSucc) (hI i.castSucc) (hle i),
    fun i => inferInstance, ?_, fun i => HQ.mkB_surjective _ _,
    fun i => HQ.factor_surjective _ _ _ _ _, fun i => HQ.factor_comp _ _ _ _ _,
    HQ.mkB_bijective_of_bot _ _ hIlast, ?_, fun hc i => @HQ.isCocomm _ _ _ _ _ _ _ hc, ?_⟩
  ·
    intro i
    by_cases hi : i = Fin.last n
    · exact HQ.flat_of_eq_bot _ _ (by rw [hi, hIlast])
    · exact HQ.flat_of_eq_J hR (S i) _ _ (hIJ i hi)
  ·
    intro i f
    rw [HQ.exists_factor_iff]
    by_cases hi : i = Fin.last n
    · subst hi
      rw [hIlast, htop]
      simp only [AddSubgroup.mem_top, iff_true]
      intro a ha
      rw [(Submodule.mem_bot R).mp ha, map_zero]
    · rw [hIJ i hi]
      constructor
      · intro hf
        exact mem_of_vanish hfix hR (S i) (hSgal i) f hf
      · intro hf a ha
        exact mem_J.mp ha f hf
  ·
    intro hfin i
    refine ⟨inferInstance, fun hi => ?_⟩
    haveI : Fintype (S i) := Fintype.ofFinite _
    rw [HQ.finrank_of_eq_J hfix hR (S i) (hSgal i) _ _ (hIJ i hi), ← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun g => ⟨e (WithConv.toConv g.1), g.2⟩
        invFun := fun m => ⟨(e.symm m.1).ofConv, ?_⟩
        left_inv := fun g => by simp
        right_inv := fun m => by simp }
    show e (WithConv.toConv (WithConv.ofConv _)) ∈ N i
    rw [WithConv.toConv_ofConv, e.apply_symm_apply]
    exact m.2

end Main
p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ"

end S17.QuotientFlagGen
p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17 P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17.QuotientFlagGen.HQ P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.S17"

theorem solution
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Algebra R L]
    (hR : Function.Injective (algebraMap R L))
    (hfix : ∀ c : L, (∀ σ : L ≃ₐ[K] L, (∀ r : R, σ (algebraMap R L r) = algebraMap R L r) → σ c = c) →
      ∃ a b : R, algebraMap R L b ≠ 0 ∧ c * algebraMap R L b = algebraMap R L a)
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    (M : Type) [AddCommGroup M] [Finite M]
    (e : WithConv (H →ₐ[R] L) ≃ M)
    (he : ∀ f g, e (f * g) = e f + e g)
    (act : (L ≃ₐ[K] L) → M → M)
    (hact : ∀ (σ : L ≃ₐ[K] L) (f g : WithConv (H →ₐ[R] L)),
        (∀ h : H, g h = σ (f h)) → e g = act σ (e f))
    (n : ℕ) (N : Fin (n + 1) → AddSubgroup M)
    (hmono : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (htop : N (Fin.last n) = ⊤)
    (hstab : ∀ (i : Fin (n + 1)) (σ : L ≃ₐ[K] L) (x : M), x ∈ N i → act σ x ∈ N i) :
    ∃ (B : Fin (n + 1) → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, HopfAlgebra R (B i))
      (π : ∀ i, H →ₐc[R] B i) (φ : ∀ i : Fin n, B i.succ →ₐc[R] B i.castSucc),
      (∀ i, Algebra.FiniteType R (B i)) ∧ (∀ i, Module.Flat R (B i)) ∧
      (∀ i, Function.Surjective (π i)) ∧ (∀ i, Function.Surjective (φ i)) ∧
      (∀ i : Fin n, (φ i).comp (π i.succ) = π i.castSucc) ∧
      Function.Bijective (π (Fin.last n)) ∧
      (∀ (i : Fin (n + 1)) (f : H →ₐ[R] L),
        (∃ g : B i →ₐ[R] L, g.comp (π i : H →ₐ[R] B i) = f) ↔
          e (WithConv.toConv f) ∈ N i) ∧
      (Coalgebra.IsCocomm R H → ∀ i, Coalgebra.IsCocomm R (B i)) ∧
      (Module.Finite R H → ∀ i, Module.Finite R (B i) ∧
        (i ≠ Fin.last n → Module.finrank R (B i) = Nat.card (N i))) :=
  S17.QuotientFlagGen.main R hR hfix H M e he act hact n N hmono htop hstab

end
end S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints
end P2MW
export P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints (solution)

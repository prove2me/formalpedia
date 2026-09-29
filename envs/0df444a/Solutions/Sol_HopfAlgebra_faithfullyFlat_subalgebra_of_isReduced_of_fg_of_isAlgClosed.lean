-- Prove2me | solution 1 for HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/09bb98d4-b12e-53bb-9bf7-a04ace544d3d

import Mathlib
import Theorems.Thm_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq
import Theorems.Thm_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal
import Theorems.Thm_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed
import Theorems.Thm_Module_Flat_isOpen_setOf_flat_localization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed

set_option autoImplicit false

open scoped TensorProduct

universe u v w

set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace TakK

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable (K : Subalgebra k H)

abbrev ι : ↥K →ₗ[k] H := K.val.toLinearMap

abbrev ι₂ : ↥K ⊗[k] ↥K →ₗ[k] H ⊗[k] H := TensorProduct.map (ι K) (ι K)

theorem ι_injective : Function.Injective (ι K) := Subtype.val_injective

theorem map_injective_of_injective {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup Q] [Module k M] [Module k N] [Module k P] [Module k Q]
    (f : M →ₗ[k] P) (g : N →ₗ[k] Q) (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  rw [← LinearMap.rTensor_comp_lTensor]
  exact (Module.Flat.rTensor_preserves_injective_linearMap f hf).comp
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)

theorem ι₂_injective : Function.Injective (ι₂ K) :=
  map_injective_of_injective _ _ (ι_injective K) (ι_injective K)

theorem ι₂_tmul (a b : ↥K) : ι₂ K (a ⊗ₜ[k] b) = (a : H) ⊗ₜ[k] (b : H) := rfl

theorem span_le_range_ι₂ :
    Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b} ≤ LinearMap.range (ι₂ K) := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact ⟨⟨a, ha⟩ ⊗ₜ[k] ⟨b, hb⟩, rfl⟩

section comul
variable (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
include hΔ

theorem comul_mem_range (x : ↥K) : Coalgebra.comul (R := k) (x : H) ∈ LinearMap.range (ι₂ K) :=
  span_le_range_ι₂ K (hΔ x x.2)

noncomputable def comulLin : ↥K →ₗ[k] ↥K ⊗[k] ↥K :=
  (LinearEquiv.ofInjective (ι₂ K) (ι₂_injective K)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (ι₂ K)) (Coalgebra.comul ∘ₗ ι K) (comul_mem_range K hΔ)

@[scoped simp] theorem ι₂_comulLin (x : ↥K) : ι₂ K (comulLin K hΔ x) = Coalgebra.comul (R := k) (x : H) := by
  simp only [comulLin, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← LinearEquiv.ofInjective_apply (ι₂ K) (h := ι₂_injective K), LinearEquiv.apply_symm_apply]
  rfl

end comul

def counitLin : ↥K →ₗ[k] k := Coalgebra.counit ∘ₗ ι K

@[scoped simp] theorem counitLin_apply (x : ↥K) : counitLin K x = Coalgebra.counit (R := k) (x : H) := rfl

theorem map_ι₂_ι_rTensor {f : ↥K →ₗ[k] ↥K ⊗[k] ↥K} {F : H →ₗ[k] H ⊗[k] H}
    (hfF : ∀ x, ι₂ K (f x) = F (x : H)) (z : ↥K ⊗[k] ↥K) :
    TensorProduct.map (ι₂ K) (ι K) (LinearMap.rTensor (↥K) f z) = LinearMap.rTensor H F (ι₂ K z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul, hfF]; rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem map_ι_ι₂_lTensor {f : ↥K →ₗ[k] ↥K ⊗[k] ↥K} {F : H →ₗ[k] H ⊗[k] H}
    (hfF : ∀ x, ι₂ K (f x) = F (x : H)) (z : ↥K ⊗[k] ↥K) :
    TensorProduct.map (ι K) (ι₂ K) (LinearMap.lTensor (↥K) f z) = LinearMap.lTensor H F (ι₂ K z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul, hfF]; rfl
  | add a b ha hb => simp only [map_add, ha, hb]

set_option maxHeartbeats 1600000 in
theorem map_ι_ι₂_assoc (w : (↥K ⊗[k] ↥K) ⊗[k] ↥K) :
    TensorProduct.map (ι K) (ι₂ K) (TensorProduct.assoc k _ _ _ w) =
      TensorProduct.assoc k H H H (TensorProduct.map (ι₂ K) (ι K) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z c =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | tmul a b => simp only [TensorProduct.assoc_tmul, TensorProduct.map_tmul]
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ι₃_injective : Function.Injective (TensorProduct.map (ι K) (ι₂ K)) :=
  map_injective_of_injective _ _ (ι_injective K) (ι₂_injective K)

theorem lTensor_ι_rTensor_counit (z : ↥K ⊗[k] ↥K) :
    LinearMap.lTensor k (ι K) (LinearMap.rTensor (↥K) (counitLin K) z) =
      LinearMap.rTensor H Coalgebra.counit (ι₂ K z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul, counitLin_apply]; rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem rTensor_ι_lTensor_counit (z : ↥K ⊗[k] ↥K) :
    LinearMap.rTensor k (ι K) (LinearMap.lTensor (↥K) (counitLin K) z) =
      LinearMap.lTensor H Coalgebra.counit (ι₂ K z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul, counitLin_apply]; rfl
  | add a b ha hb => simp only [map_add, ha, hb]

section structures
variable (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})

@[reducible] noncomputable def coalgebraStruct : CoalgebraStruct k ↥K where
  comul := comulLin K hΔ
  counit := counitLin K

set_option maxHeartbeats 1600000 in

@[reducible] noncomputable def coalgebra : Coalgebra k ↥K :=
  { coalgebraStruct K hΔ with
    coassoc := by
      apply LinearMap.ext
      intro x
      apply ι₃_injective K
      change TensorProduct.map (ι K) (ι₂ K) (TensorProduct.assoc k _ _ _
          (LinearMap.rTensor (↥K) (comulLin K hΔ) (comulLin K hΔ x))) =
        TensorProduct.map (ι K) (ι₂ K) (LinearMap.lTensor (↥K) (comulLin K hΔ) (comulLin K hΔ x))
      rw [map_ι_ι₂_assoc, map_ι₂_ι_rTensor K (ι₂_comulLin K hΔ), map_ι_ι₂_lTensor K (ι₂_comulLin K hΔ),
        ι₂_comulLin, Coalgebra.coassoc_apply]
    rTensor_counit_comp_comul := by
      apply LinearMap.ext
      intro x
      apply Module.Flat.lTensor_preserves_injective_linearMap (M := k) (ι K) (ι_injective K)
      change LinearMap.lTensor k (ι K) (LinearMap.rTensor (↥K) (counitLin K) (comulLin K hΔ x)) =
        LinearMap.lTensor k (ι K) ((1 : k) ⊗ₜ[k] x)
      rw [lTensor_ι_rTensor_counit, ι₂_comulLin, Coalgebra.rTensor_counit_comul]
      simp
    lTensor_counit_comp_comul := by
      apply LinearMap.ext
      intro x
      apply Module.Flat.rTensor_preserves_injective_linearMap (M := k) (ι K) (ι_injective K)
      change LinearMap.rTensor k (ι K) (LinearMap.lTensor (↥K) (counitLin K) (comulLin K hΔ x)) =
        LinearMap.rTensor k (ι K) (x ⊗ₜ[k] (1 : k))
      rw [rTensor_ι_lTensor_counit, ι₂_comulLin, Coalgebra.lTensor_counit_comul]
      simp }

end structures

theorem ι₂_eq_toLinearMap :
    ι₂ K = (Algebra.TensorProduct.map K.val K.val).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  rfl

theorem ι₂_mul (z w : ↥K ⊗[k] ↥K) : ι₂ K (z * w) = ι₂ K z * ι₂ K w := by
  rw [ι₂_eq_toLinearMap]
  exact map_mul (Algebra.TensorProduct.map K.val K.val) z w

theorem ι₂_one : ι₂ K 1 = 1 := by
  rw [ι₂_eq_toLinearMap]
  exact map_one (Algebra.TensorProduct.map K.val K.val)

section structures2
variable (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})

theorem comulLin_mul (a b : ↥K) : comulLin K hΔ (a * b) = comulLin K hΔ a * comulLin K hΔ b := by
  apply ι₂_injective K
  rw [ι₂_mul, ι₂_comulLin, ι₂_comulLin, ι₂_comulLin, Subalgebra.coe_mul, Bialgebra.comul_mul]

theorem comulLin_one : comulLin K hΔ 1 = 1 := by
  apply ι₂_injective K
  rw [ι₂_comulLin, ι₂_one, Subalgebra.coe_one, Bialgebra.comul_one]

@[reducible] noncomputable def bialgebra : Bialgebra k ↥K :=
  { coalgebra K hΔ with
    counit_one := by
      change counitLin K 1 = 1
      rw [counitLin_apply, Subalgebra.coe_one, Bialgebra.counit_one]
    mul_compr₂_counit := by
      apply LinearMap.ext; intro a; apply LinearMap.ext; intro b
      change counitLin K (a * b) = counitLin K a * counitLin K b
      rw [counitLin_apply, counitLin_apply, counitLin_apply, Subalgebra.coe_mul, Bialgebra.counit_mul]
    comul_one := comulLin_one K hΔ
    mul_compr₂_comul := by
      apply LinearMap.ext; intro a; apply LinearMap.ext; intro b
      exact comulLin_mul K hΔ a b }

variable (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)

def antipodeLin : ↥K →ₗ[k] ↥K :=
  LinearMap.codRestrict K.toSubmodule ((HopfAlgebra.antipode k).comp (ι K)) (fun x => hS x x.2)

@[scoped simp] theorem coe_antipodeLin (x : ↥K) : (antipodeLin K hS x : H) = HopfAlgebra.antipode k (x : H) := rfl

theorem ι_mul'_rTensor (z : ↥K ⊗[k] ↥K) :
    ι K (LinearMap.mul' k ↥K (LinearMap.rTensor (↥K) (antipodeLin K hS) z)) =
      LinearMap.mul' k H (LinearMap.rTensor H (HopfAlgebra.antipode k) (ι₂ K z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ι_mul'_lTensor (z : ↥K ⊗[k] ↥K) :
    ι K (LinearMap.mul' k ↥K (LinearMap.lTensor (↥K) (antipodeLin K hS) z)) =
      LinearMap.mul' k H (LinearMap.lTensor H (HopfAlgebra.antipode k) (ι₂ K z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

set_option maxHeartbeats 1600000 in

@[reducible] noncomputable def hopfAlgebra : HopfAlgebra k ↥K :=
  { bialgebra K hΔ with
    antipode := antipodeLin K hS
    mul_antipode_rTensor_comul := by
      apply LinearMap.ext; intro x
      apply ι_injective K
      change ι K (LinearMap.mul' k ↥K (LinearMap.rTensor (↥K) (antipodeLin K hS) (comulLin K hΔ x))) =
        ι K (algebraMap k ↥K (counitLin K x))
      rw [ι_mul'_rTensor, ι₂_comulLin, HopfAlgebra.mul_antipode_rTensor_comul_apply, counitLin_apply]
      rfl
    mul_antipode_lTensor_comul := by
      apply LinearMap.ext; intro x
      apply ι_injective K
      change ι K (LinearMap.mul' k ↥K (LinearMap.lTensor (↥K) (antipodeLin K hS) (comulLin K hΔ x))) =
        ι K (algebraMap k ↥K (counitLin K x))
      rw [ι_mul'_lTensor, ι₂_comulLin, HopfAlgebra.mul_antipode_lTensor_comul_apply, counitLin_apply]
      rfl }

theorem val_comul (x : ↥K) :
    letI := hopfAlgebra K hΔ hS
    Coalgebra.comul (R := k) (x : H) =
      TensorProduct.map (IsScalarTower.toAlgHom k ↥K H).toLinearMap (IsScalarTower.toAlgHom k ↥K H).toLinearMap
        (Coalgebra.comul (R := k) x) := by
  letI := hopfAlgebra K hΔ hS
  change Coalgebra.comul (R := k) (x : H) = TensorProduct.map _ _ (comulLin K hΔ x)
  rw [← ι₂_comulLin K hΔ x]
  rfl

theorem val_counit (x : ↥K) :
    letI := hopfAlgebra K hΔ hS
    Coalgebra.counit (R := k) (x : H) = Coalgebra.counit (R := k) x := rfl

theorem val_antipode (x : ↥K) :
    letI := hopfAlgebra K hΔ hS
    ((HopfAlgebra.antipode k x : ↥K) : H) = HopfAlgebra.antipode k (x : H) := rfl

theorem algebraMap_injective : Function.Injective (algebraMap ↥K H) := Subtype.val_injective

end structures2

end TakK
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed.TakK"

namespace S17Red

theorem flat_transport {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (σ : A ≃+* A) (e : B ≃+* B) (hcompat : ∀ a, e (algebraMap A B a) = algebraMap A B (σ a))
    (P Q : Ideal B) [P.IsPrime] [Q.IsPrime] (hQP : ∀ x, x ∈ Q ↔ e x ∈ P)
    (hP : Module.Flat A (Localization.AtPrime P)) : Module.Flat A (Localization.AtPrime Q) := by
  have hmapS : Submonoid.map e.toMonoidHom Q.primeCompl = P.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact fun h => hx ((hQP x).mpr h)
    · intro hy
      refine ⟨e.symm y, fun h => hy ?_, ?_⟩
      · have := (hQP (e.symm y)).mp h
        simpa using this
      · simp
  let eLoc : Localization.AtPrime Q ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv (M := Q.primeCompl) (T := P.primeCompl)
      (Localization.AtPrime Q) (Localization.AtPrime P) e hmapS
  have hsq : ∀ x : A, eLoc (algebraMap A (Localization.AtPrime Q) x) =
      algebraMap A (Localization.AtPrime P) (σ x) := by
    intro x
    rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q),
      IsScalarTower.algebraMap_apply A B (Localization.AtPrime P),
      IsLocalization.ringEquivOfRingEquiv_eq, hcompat]
  have hflatP : (algebraMap A (Localization.AtPrime P)).Flat := RingHom.flat_algebraMap_iff.mpr hP
  have hcomp : algebraMap A (Localization.AtPrime Q) =
      (eLoc.symm.toRingHom.comp (algebraMap A (Localization.AtPrime P))).comp (σ : A →+* A) := by
    apply RingHom.ext
    intro x
    change algebraMap A (Localization.AtPrime Q) x = eLoc.symm (algebraMap A (Localization.AtPrime P) (σ x))
    rw [← hsq, RingEquiv.symm_apply_apply]
  rw [← RingHom.flat_algebraMap_iff, hcomp]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective σ.bijective)
    (RingHom.Flat.comp hflatP (RingHom.Flat.of_bijective eLoc.symm.bijective))

theorem exists_flat_localization_atPrime_of_isReduced_of_injective
    (K : Type v) [CommRing K] [IsReduced K]
    (H : Type w) [CommRing H] [Nontrivial H] [Algebra K H] (hinj : Function.Injective (algebraMap K H)) :
    ∃ Q : PrimeSpectrum H, Module.Flat K (Localization.AtPrime Q.asIdeal) := by
  classical
  haveI : Nontrivial K := (algebraMap K H).domain_nontrivial

  obtain ⟨⟨p, hp⟩⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal K)) bot_ne_top
  have hp' : p ∈ minimalPrimes K := hp
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hinj p hp'
  haveI : p.IsPrime := hp.1.1
  haveI : Q.IsPrime := hQ
  refine ⟨⟨Q, hQ⟩, ?_⟩

  let Kp := Localization.AtPrime p
  haveI : Ring.KrullDimLE 0 Kp := Ring.KrullDimLE.of_isLocalization p hp' Kp
  haveI : IsReduced Kp := inferInstance
  have hfield : IsField Kp := Ring.KrullDimLE.isField_of_isReduced
  letI : Field Kp := hfield.toField

  let φ : Kp →+* Localization.AtPrime Q := Localization.localRingHom p Q (algebraMap K H) hQp.symm
  letI : Algebra Kp (Localization.AtPrime Q) := φ.toAlgebra
  haveI : IsScalarTower K Kp (Localization.AtPrime Q) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    show algebraMap K (Localization.AtPrime Q) x = φ (algebraMap K Kp x)
    rw [Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply K H (Localization.AtPrime Q)]

  haveI : Module.Flat K Kp := IsLocalization.flat Kp p.primeCompl
  haveI : Module.Flat Kp (Localization.AtPrime Q) := inferInstance
  exact Module.Flat.trans K Kp (Localization.AtPrime Q)

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]

theorem exists_algHom_ker_eq [IsAlgClosed k] [Algebra.FiniteType k H] (M : Ideal H) [hM : M.IsMaximal] :
    ∃ x : H →ₐ[k] k, RingHom.ker x = M := by
  letI : Field (H ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite k (H ⧸ M) := finite_of_finite_type_of_isJacobsonRing k (H ⧸ M)
  haveI : Algebra.IsIntegral k (H ⧸ M) := inferInstance
  let e : k ≃ₐ[k] (H ⧸ M) :=
    AlgEquiv.ofBijective (Algebra.ofId k (H ⧸ M)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k M), ?_⟩
  ext h
  simp only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [show (e.symm.toAlgHom (Ideal.Quotient.mk M h) = 0) ↔ (Ideal.Quotient.mk M h = 0) from
    ⟨fun h0 => by simpa using congrArg e h0, fun h0 => by rw [h0, map_zero]⟩]
  exact Ideal.Quotient.eq_zero_iff_mem

noncomputable def τ (g : H →ₐ[k] k) : H →ₐ[k] H :=
  (Algebra.TensorProduct.lid k H).toAlgHom.comp
    ((Algebra.TensorProduct.map g (AlgHom.id k H)).comp (Bialgebra.comulAlgHom k H))

theorem τ_spec (g : H →ₐ[k] k) (h : H) :
    τ g h = Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map g (AlgHom.id k H) (Coalgebra.comul h)) := rfl

end S17Red
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed.TakK"

set_option maxHeartbeats 1600000 in
p2m_attr_erase "instance" "Subalgebra.moduleLeft in"
open S17Red in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    (hfg : K.FG) [IsReduced ↥K] :
    Module.FaithfullyFlat ↥K H := by
  classical

  letI hK : HopfAlgebra k ↥K := TakK.hopfAlgebra K hΔ hS
  haveI : Algebra.FiniteType k ↥K := (Subalgebra.fg_iff_finiteType K).mp hfg
  haveI : IsNoetherianRing ↥K := Algebra.FiniteType.isNoetherianRing k ↥K
  haveI : Algebra.FiniteType ↥K H := Algebra.FiniteType.of_restrictScalars_finiteType k ↥K H
  haveI : IsJacobsonRing H := isJacobsonRing_of_finiteType (A := k) (B := H)
  have hinj : Function.Injective (algebraMap ↥K H) := Subtype.val_injective
  have hH : Nontrivial H := ⟨⟨1, 0, fun h10 => by
    have := Bialgebra.counit_one (R := k) (A := H)
    rw [h10, map_zero] at this
    exact zero_ne_one this⟩⟩

  obtain ⟨hτbij, hτmem, hτtrans⟩ :=
    HopfAlgebra.bijective_translate_and_map_mem_and_exists_comp_translate_eq (k := k) (H := H) τ τ_spec
  let τK : (↥K →ₐ[k] k) → (↥K →ₐ[k] ↥K) := fun g =>
    (Algebra.TensorProduct.lid k ↥K).toAlgHom.comp
      ((Algebra.TensorProduct.map g (AlgHom.id k ↥K)).comp (Bialgebra.comulAlgHom k ↥K))
  obtain ⟨hτKbij, -, -⟩ :=
    HopfAlgebra.bijective_translate_and_map_mem_and_exists_comp_translate_eq (k := k) (H := ↥K) τK (fun g h => rfl)

  have hτK : ∀ (g : H →ₐ[k] k) (x : ↥K), ((τK (g.comp K.val) x : ↥K) : H) = τ g x := by
    intro g x
    change ((Algebra.TensorProduct.lid k ↥K (Algebra.TensorProduct.map (g.comp K.val) (AlgHom.id k ↥K)
      (Coalgebra.comul (R := k) x)) : ↥K) : H) =
      Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map g (AlgHom.id k H) (Coalgebra.comul (R := k) (x : H)))
    rw [TakK.val_comul K hΔ hS x]
    induction (Coalgebra.comul (R := k) x) using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.coe_id, id_eq, IsScalarTower.coe_toAlgHom',
        Subalgebra.coe_smul]
      rfl
    | add a b ha hb =>
      simp only [map_add, Subalgebra.coe_add, ha, hb]

  have hUopen : IsOpen {Q : PrimeSpectrum H | Module.Flat ↥K (Localization.AtPrime Q.asIdeal)} :=
    Module.Flat.isOpen_setOf_flat_localization_atPrime (A := ↥K) (B := H)
  have hUne : ({Q : PrimeSpectrum H | Module.Flat ↥K (Localization.AtPrime Q.asIdeal)}).Nonempty := by
    obtain ⟨Q, hQ⟩ := exists_flat_localization_atPrime_of_isReduced_of_injective ↥K H hinj
    exact ⟨Q, hQ⟩
  have hUtrans : ∀ P Q : PrimeSpectrum H, P.asIdeal.IsMaximal → Q.asIdeal.IsMaximal →
      P ∈ {Q : PrimeSpectrum H | Module.Flat ↥K (Localization.AtPrime Q.asIdeal)} → Q ∈ {Q : PrimeSpectrum H | Module.Flat ↥K (Localization.AtPrime Q.asIdeal)} := by
    intro P Q hP hQ hPU
    haveI := hP; haveI := hQ
    obtain ⟨xP, hxP⟩ := exists_algHom_ker_eq (k := k) P.asIdeal
    obtain ⟨xQ, hxQ⟩ := exists_algHom_ker_eq (k := k) Q.asIdeal
    obtain ⟨g, hg⟩ := hτtrans xP xQ
    let e : H ≃ₐ[k] H := AlgEquiv.ofBijective (τ g) (hτbij g)
    have he : ∀ h, e h = τ g h := fun _ => rfl
    have hQP : ∀ x : H, x ∈ Q.asIdeal ↔ e x ∈ P.asIdeal := by
      intro x
      rw [← hxQ, ← hxP, hg, RingHom.mem_ker, RingHom.mem_ker, he]
      rfl

    let σ : ↥K ≃ₐ[k] ↥K := AlgEquiv.ofBijective (τK (g.comp K.val)) (hτKbij _)
    have hσ : ∀ x : ↥K, ((σ x : ↥K) : H) = e x := fun x => hτK g x
    have hPU' : Module.Flat ↥K (Localization.AtPrime P.asIdeal) := hPU
    haveI : P.asIdeal.IsPrime := hP.isPrime
    haveI : Q.asIdeal.IsPrime := hQ.isPrime
    exact flat_transport (A := ↥K) (B := H) σ.toRingEquiv e.toRingEquiv (fun a => (hσ a).symm)
      P.asIdeal Q.asIdeal hQP hPU'
  have hU : {Q : PrimeSpectrum H | Module.Flat ↥K (Localization.AtPrime Q.asIdeal)} = Set.univ :=
    PrimeSpectrum.eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal _ hUopen hUne hUtrans
  haveI hflat : Module.Flat ↥K H := by
    apply Module.flat_of_isLocalized_maximal H H (fun P _ => Localization.AtPrime P)
      (fun P _ => Algebra.linearMap H (Localization.AtPrime P))
    intro P hP
    have hmem : (⟨P, hP.isPrime⟩ : PrimeSpectrum H) ∈ {Q : PrimeSpectrum H | Module.Flat ↥K (Localization.AtPrime Q.asIdeal)} := by
      rw [hU]; trivial
    exact hmem

  exact HopfAlgebra.faithfullyFlat_of_flat_of_injective_of_isAlgClosed ↥K H hinj
    (fun x => TakK.val_comul K hΔ hS x) (fun x => TakK.val_counit K hΔ hS x)

end S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed
end P2MW
export P2MW.S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed (solution)

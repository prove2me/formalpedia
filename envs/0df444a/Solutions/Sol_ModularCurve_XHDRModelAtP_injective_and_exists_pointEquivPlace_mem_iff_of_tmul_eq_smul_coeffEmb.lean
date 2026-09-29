-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.injective_and_exists_pointEquivPlace_mem_iff_of_tmul_eq_smul_coeffEmb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4cf47018-14d6-54ea-912e-df87d3a11da7

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_injective_and_exists_pointEquivPlace_mem_iff_of_tmul_eq_smul_coeffEmb

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel

namespace XLocalC4

noncomputable def plToQ (p : ℕ) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ) : ↥Pl →ₐ[R p] AlgebraicClosure ℚ where
  toRingHom := Pl.subtype
  commutes' r := by
    have h := congrArg (fun f : R p →+* AlgebraicClosure ℚ => f r) hρ
    simp only [RingHom.coe_comp, Function.comp_apply] at h
    rw [halg]
    exact h

theorem plToQ_apply (p : ℕ) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ) (π : ↥Pl) :
    plToQ p Pl ρ hρ halg π = (π : AlgebraicClosure ℚ) := rfl

noncomputable def dictι (p : ℕ) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)
    (B : Type) [CommRing B] [Algebra (R p) B] :
    ↥Pl ⊗[R p] B →ₐ[R p] AlgebraicClosure ℚ ⊗[R p] B :=
  Algebra.TensorProduct.map (plToQ p Pl ρ hρ halg) (AlgHom.id (R p) B)

@[scoped simp] theorem dictι_tmul (p : ℕ) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)
    (B : Type) [CommRing B] [Algebra (R p) B] (π : ↥Pl) (b : B) :
    dictι p Pl ρ hρ halg B (π ⊗ₜ[R p] b) = (π : AlgebraicClosure ℚ) ⊗ₜ[R p] b := rfl

theorem dict_flat (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (B : Subalgebra (R p) ↥(qExpFunctionFieldC ℚ Γ)) :
    Module.Flat (R p) ↥B := by
  haveI : IsPrincipalIdealRing (R p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  have hinj : Function.Injective (algebraMap (R p) ↥(qExpFunctionFieldC ℚ Γ)) := by
    rw [IsScalarTower.algebraMap_eq (R p) ℚ ↥(qExpFunctionFieldC ℚ Γ)]
    exact (algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ)).injective.comp Subtype.val_injective
  haveI : Module.IsTorsionFree (R p) ↥(qExpFunctionFieldC ℚ Γ) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
  haveI : Module.IsTorsionFree (R p) ↥B :=
    Function.Injective.moduleIsTorsionFree (fun b : ↥B => (b : ↥(qExpFunctionFieldC ℚ Γ))) Subtype.val_injective
      (fun _ _ => rfl)
  haveI : IsDedekindDomain (R p) := IsPrincipalIdealRing.isDedekindDomain (R p)
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

theorem dict_ι_injective (p : ℕ) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)
    (B : Type) [CommRing B] [Algebra (R p) B] [Module.Flat (R p) B] :
    Function.Injective (dictι p Pl ρ hρ halg B) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := B) (plToQ p Pl ρ hρ halg).toLinearMap
    Subtype.val_injective
  intro x y hxy
  exact h hxy

theorem dict_exists_mul_eq_one (p : ℕ) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)
    (B : Type) [CommRing B] [Algebra (R p) B] (z : AlgebraicClosure ℚ ⊗[R p] B) :
    ∃ (π : ↥Pl) (a : ↥Pl ⊗[R p] B), π ≠ 0 ∧
      dictι p Pl ρ hρ halg B a = ((π : AlgebraicClosure ℚ) ⊗ₜ[R p] (1 : B)) * z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q b =>
    obtain ⟨⟨x, ⟨d, hd⟩⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors ↥Pl) (S := AlgebraicClosure ℚ) q

    refine ⟨d, x ⊗ₜ[R p] b, nonZeroDivisors.ne_zero hd, ?_⟩
    rw [dictι_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    simp only at hq
    rw [mul_comm] at hq
    exact hq.symm
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨π₁, a₁, hπ₁, ha₁⟩ := h₁
    obtain ⟨π₂, a₂, hπ₂, ha₂⟩ := h₂
    refine ⟨π₁ * π₂, (π₂ ⊗ₜ[R p] (1 : B)) * a₁ + (π₁ ⊗ₜ[R p] (1 : B)) * a₂, mul_ne_zero hπ₁ hπ₂, ?_⟩
    rw [map_add, map_mul, map_mul, dictι_tmul, dictι_tmul, ha₁, ha₂, mul_add, Subring.coe_mul]
    simp only [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm (π₂ : AlgebraicClosure ℚ)]

theorem dict_exists_mul_eq (p : ℕ) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)
    (B : Type) [CommRing B] [Algebra (R p) B] (a' s' : AlgebraicClosure ℚ ⊗[R p] B) :
    ∃ (π : ↥Pl) (a s : ↥Pl ⊗[R p] B), π ≠ 0 ∧
      dictι p Pl ρ hρ halg B a = ((π : AlgebraicClosure ℚ) ⊗ₜ[R p] (1 : B)) * a' ∧
      dictι p Pl ρ hρ halg B s = ((π : AlgebraicClosure ℚ) ⊗ₜ[R p] (1 : B)) * s' := by
  obtain ⟨π₁, a₁, hπ₁, ha₁⟩ := dict_exists_mul_eq_one p Pl ρ hρ halg B a'
  obtain ⟨π₂, s₁, hπ₂, hs₁⟩ := dict_exists_mul_eq_one p Pl ρ hρ halg B s'
  refine ⟨π₁ * π₂, (π₂ ⊗ₜ[R p] (1 : B)) * a₁, (π₁ ⊗ₜ[R p] (1 : B)) * s₁, mul_ne_zero hπ₁ hπ₂, ?_, ?_⟩
  · rw [map_mul, dictι_tmul, ha₁, Subring.coe_mul, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm (π₂ : AlgebraicClosure ℚ)]
  · rw [map_mul, dictι_tmul, hs₁, Subring.coe_mul, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem dict_isLocalization (p : ℕ) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)
    (B : Type) [CommRing B] [Algebra (R p) B] [Module.Flat (R p) B] :
    letI : Algebra (↥Pl ⊗[R p] B) (AlgebraicClosure ℚ ⊗[R p] B) := (dictι p Pl ρ hρ halg B).toRingHom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (↥Pl ⊗[R p] B) (nonZeroDivisors ↥Pl)) (AlgebraicClosure ℚ ⊗[R p] B) := by
  letI : Algebra (↥Pl ⊗[R p] B) (AlgebraicClosure ℚ ⊗[R p] B) := (dictι p Pl ρ hρ halg B).toRingHom.toAlgebra
  have halgmap : ∀ a, algebraMap (↥Pl ⊗[R p] B) (AlgebraicClosure ℚ ⊗[R p] B) a = dictι p Pl ρ hρ halg B a := fun _ => rfl
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, π, hπ, rfl⟩
    rw [halgmap]
    show IsUnit (dictι p Pl ρ hρ halg B ((π : ↥Pl) ⊗ₜ[R p] (1 : B)))
    rw [dictι_tmul]
    have hπ0 : (π : AlgebraicClosure ℚ) ≠ 0 := by
      have := nonZeroDivisors.ne_zero hπ
      exact fun h => this (Subtype.ext h)
    exact (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := AlgebraicClosure ℚ) (B := B)).isUnit_map
      (IsUnit.mk0 _ hπ0)
  · intro z
    obtain ⟨π, a, hπ, ha⟩ := dict_exists_mul_eq_one p Pl ρ hρ halg B z
    refine ⟨⟨a, ⟨π ⊗ₜ[R p] (1 : B), π, mem_nonZeroDivisors_of_ne_zero hπ, rfl⟩⟩, ?_⟩
    simp only [halgmap, dictι_tmul]
    rw [mul_comm]
    exact ha.symm
  · intro x y hxy
    refine ⟨1, ?_⟩
    rw [halgmap, halgmap] at hxy
    simpa using dict_ι_injective p Pl ρ hρ halg B hxy

theorem dict_exists_isPrime_comap_eq (p : ℕ) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)
    (B : Type) [CommRing B] [Algebra (R p) B] [Module.Flat (R p) B]
    (𝔮 : Ideal (↥Pl ⊗[R p] B)) (h𝔮 : 𝔮.IsPrime)
    (h0 : 𝔮.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥Pl) (B := B)) = ⊥) :
    ∃ 𝔮' : Ideal (AlgebraicClosure ℚ ⊗[R p] B), 𝔮'.IsPrime ∧
      𝔮'.comap (dictι p Pl ρ hρ halg B).toRingHom = 𝔮 := by
  letI : Algebra (↥Pl ⊗[R p] B) (AlgebraicClosure ℚ ⊗[R p] B) := (dictι p Pl ρ hρ halg B).toRingHom.toAlgebra
  haveI := dict_isLocalization p Pl ρ hρ halg B
  have hdisj : Disjoint ((Algebra.algebraMapSubmonoid (↥Pl ⊗[R p] B) (nonZeroDivisors ↥Pl) : Set _) : Set (↥Pl ⊗[R p] B)) ↑𝔮 := by
    rw [Set.disjoint_left]
    rintro _ ⟨π, hπ, rfl⟩ hmem
    have : (π : ↥Pl) ∈ 𝔮.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥Pl) (B := B)) := hmem
    rw [h0, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hπ this
  refine ⟨𝔮.map (algebraMap (↥Pl ⊗[R p] B) (AlgebraicClosure ℚ ⊗[R p] B)),
    IsLocalization.isPrime_of_isPrime_disjoint _ (AlgebraicClosure ℚ ⊗[R p] B) 𝔮 h𝔮 hdisj, ?_⟩
  exact IsLocalization.under_map_of_isPrime_disjoint _ (AlgebraicClosure ℚ ⊗[R p] B) h𝔮 hdisj

section Stalk
universe u v

theorem dict_Ψ_injective {Y : Scheme.{u}} [IsIntegral Y] {U : Y.Opens} [Nonempty U]
    {T : Type u} [CommRing T] (θ : Γ(Y, U) ≅ CommRingCat.of T)
    {F : Type v} [Field F] (ff : Y.functionField ≃+* F) :
    Function.Injective
      ((ff : Y.functionField ≃+* F).toRingHom.comp ((Y.germToFunctionField U).hom.comp θ.inv.hom)) := by
  rw [RingHom.coe_comp, RingHom.coe_comp]
  exact ff.injective.comp ((Scheme.germToFunctionField_injective Y U).comp θ.symm.commRingCatIsoToRingEquiv.injective)

theorem dict_Ψ_apply_hom {Y : Scheme.{u}} [IsIntegral Y] {U : Y.Opens} [Nonempty U]
    {T : Type u} [CommRing T] (θ : Γ(Y, U) ≅ CommRingCat.of T)
    {F : Type v} [Field F] (ff : Y.functionField ≃+* F) (x : Γ(Y, U)) :
    ((ff : Y.functionField ≃+* F).toRingHom.comp ((Y.germToFunctionField U).hom.comp θ.inv.hom)) (θ.hom.hom x) =
      ff (Y.germToFunctionField U x) := by
  show ff ((Y.germToFunctionField U).hom (θ.inv.hom (θ.hom.hom x))) = _
  rw [← CommRingCat.comp_apply θ.hom θ.inv, θ.hom_inv_id, CommRingCat.id_apply]

theorem dict_exists_mul_Ψ_eq {Y : Scheme.{u}} [IsIntegral Y] {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U]
    {T : Type u} [CommRing T] (θ : Γ(Y, U) ≅ CommRingCat.of T)
    {F : Type v} [Field F] (ff : Y.functionField ≃+* F) (k : F) :
    ∃ a s : T, s ≠ 0 ∧
      k * ((ff : Y.functionField ≃+* F).toRingHom.comp ((Y.germToFunctionField U).hom.comp θ.inv.hom)) s =
        ((ff : Y.functionField ≃+* F).toRingHom.comp ((Y.germToFunctionField U).hom.comp θ.inv.hom)) a := by
  haveI := functionField_isFractionRing_of_isAffineOpen Y U hU
  obtain ⟨⟨x, ⟨d, hd⟩⟩, hxd⟩ := IsLocalization.surj (nonZeroDivisors Γ(Y, U)) (S := Y.functionField) (ff.symm k)

  refine ⟨θ.hom.hom x, θ.hom.hom d, ?_, ?_⟩
  · intro h0
    apply nonZeroDivisors.ne_zero hd
    exact θ.commRingCatIsoToRingEquiv.injective (by rw [map_zero]; exact h0)
  · rw [dict_Ψ_apply_hom, dict_Ψ_apply_hom]
    have e := congrArg ff hxd
    rw [map_mul, RingEquiv.apply_symm_apply] at e
    exact e

theorem dict_mem_range_stalk_iff {Y : Scheme.{u}} [IsIntegral Y] {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U]
    {T : Type u} [CommRing T] (θ : Γ(Y, U) ≅ CommRingCat.of T)
    {F : Type v} [Field F] (ff : Y.functionField ≃+* F) (P : PrimeSpectrum T) (k : F) :
    (∃ st : Y.presheaf.stalk (hU.fromSpec (Spec.map θ.hom P)),
        ff (algebraMap (Y.presheaf.stalk (hU.fromSpec (Spec.map θ.hom P))) Y.functionField st) = k) ↔
    ∃ a s : T, s ∉ P.asIdeal ∧
      k * ((ff : Y.functionField ≃+* F).toRingHom.comp ((Y.germToFunctionField U).hom.comp θ.inv.hom)) s =
        ((ff : Y.functionField ≃+* F).toRingHom.comp ((Y.germToFunctionField U).hom.comp θ.inv.hom)) a := by
  classical
  let y : PrimeSpectrum Γ(Y, U) := Spec.map θ.hom P
  have hyP : y.asIdeal = P.asIdeal.comap θ.hom.hom := rfl
  let x₀ : Y := hU.fromSpec y
  have hx₀ : x₀ ∈ U := by
    have : x₀ ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this
  letI algS : Algebra Γ(Y, U) (Y.presheaf.stalk x₀) := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨x₀, hx₀⟩
  haveI hloc : IsLocalization.AtPrime (Y.presheaf.stalk x₀) y.asIdeal := hU.isLocalization_stalk' y hx₀

  have hgermff : ∀ t : Γ(Y, U), algebraMap (Y.presheaf.stalk x₀) Y.functionField (algebraMap Γ(Y, U) (Y.presheaf.stalk x₀) t) =
      Y.germToFunctionField U t := by
    intro t
    change (Y.presheaf.stalkSpecializes (genericPoint_specializes x₀)).hom ((Y.presheaf.germ U x₀ hx₀).hom t) = _
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have hΨ := dict_Ψ_apply_hom θ ff
  constructor
  · rintro ⟨st, rfl⟩
    obtain ⟨x, d, rfl⟩ := IsLocalization.exists_mk'_eq y.asIdeal.primeCompl st
    refine ⟨θ.hom.hom x, θ.hom.hom d, ?_, ?_⟩
    · exact d.2
    · rw [hΨ, hΨ, ← hgermff, ← hgermff, ← map_mul, ← map_mul, IsLocalization.mk'_spec]
  · rintro ⟨a, s, hs, hk⟩
    have hd : θ.inv.hom s ∉ y.asIdeal := by
      rw [hyP, Ideal.mem_comap]
      intro h
      apply hs
      rwa [← CommRingCat.comp_apply, θ.inv_hom_id, CommRingCat.id_apply] at h
    refine ⟨IsLocalization.mk' (M := y.asIdeal.primeCompl) (Y.presheaf.stalk x₀) (θ.inv.hom a) ⟨θ.inv.hom s, hd⟩, ?_⟩
    have hs0 : ((ff : Y.functionField ≃+* F).toRingHom.comp ((Y.germToFunctionField U).hom.comp θ.inv.hom)) s ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := dict_Ψ_injective θ ff (by rw [h0, map_zero])
      rw [this]
      exact P.asIdeal.zero_mem
    apply mul_right_cancel₀ hs0
    rw [hk]
    show ff (algebraMap (Y.presheaf.stalk x₀) Y.functionField
        (IsLocalization.mk' (M := y.asIdeal.primeCompl) (Y.presheaf.stalk x₀) (θ.inv.hom a) ⟨θ.inv.hom s, hd⟩)) *
        ff (Y.germToFunctionField U (θ.inv.hom s)) = ff (Y.germToFunctionField U (θ.inv.hom a))
    rw [← hgermff, ← hgermff, ← map_mul, ← map_mul, IsLocalization.mk'_spec]

end Stalk

section Generic

universe u

variable {R K B : Type u} [CommRing R] [CommRing K] [CommRing B] [Algebra R K] [Algebra R B]
  {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
  (ιB : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ιB]
  (hιB : ιB ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B)))

include hιB

omit hιB in
theorem appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ h = f.appTop :=
  Scheme.Hom.appLE_eq_app _

noncomputable def bcChart :
    Spec (CommRingCat.of (K ⊗[R] B)) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  (pullbackSpecIso R K B).inv ≫
    pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R K))) (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) c (𝟙 _) ιB (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans hιB.symm) ≫
    (pullbackSymmetry _ _).hom

omit [IsOpenImmersion ιB] in
@[reassoc]
theorem bcChart_fst : bcChart c ιB hιB (K := K) ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom) ≫ ιB := by
  simp only [bcChart, Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_snd, pullbackSpecIso_inv_snd_assoc]
  rfl

omit [IsOpenImmersion ιB] in
@[reassoc]
theorem bcChart_snd : bcChart c ιB hιB (K := K) ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))) := by
  simp only [bcChart, Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst, Category.comp_id,
    pullbackSpecIso_inv_fst]

scoped instance bcChart_isOpenImmersion : IsOpenImmersion (bcChart c ιB hιB (K := K)) := by
  have : IsOpenImmersion (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) c (𝟙 _) ιB (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans hιB.symm)) :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (i₁ := 𝟙 _) (i₂ := ιB) inferInstance inferInstance
      (Category.id_comp _).symm hιB.symm
  unfold bcChart
  infer_instance

omit [IsOpenImmersion ιB] in
theorem range_bcChart : Set.range (bcChart c ιB hιB (K := K)) =
    (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹' Set.range ιB := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom) t, ?_⟩
    show _ = (bcChart c ιB hιB ≫ pullback.fst _ _) t
    rw [bcChart_fst]
    rfl
  · rintro z ⟨w, hw⟩
    set z' : ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap R K))) c) :=
      (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R K))) c).inv z with hz'def
    have hz' : z' ∈ Set.range (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) c (𝟙 _) ιB (𝟙 _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans hιB.symm)) := by
      rw [Scheme.Pullback.range_map]
      refine ⟨⟨pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K))) c z', rfl⟩, ⟨w, ?_⟩⟩
      show ιB w = ((pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R K))) c).inv ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R K))) c) z
      rw [pullbackSymmetry_inv_comp_snd]
      exact hw
    obtain ⟨t, ht⟩ := hz'
    refine ⟨(pullbackSpecIso R K B).hom t, ?_⟩
    show ((pullbackSpecIso R K B).hom ≫ bcChart c ιB hιB) t = z
    simp only [bcChart, Iso.hom_inv_id_assoc, Scheme.Hom.comp_apply, ht, hz'def]
    show ((pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R K))) c).inv ≫
      (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R K))) c).hom) z = z
    rw [Iso.inv_hom_id]
    rfl

variable {Y : Scheme.{u}} (e : Y ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e]

noncomputable def gChart : Spec (CommRingCat.of (K ⊗[R] B)) ⟶ Y := bcChart c ιB hιB ≫ inv e

scoped instance gChart_isOpenImmersion : IsOpenImmersion (gChart c ιB hιB e) := by
  unfold gChart; infer_instance

omit [IsOpenImmersion ιB] in
@[reassoc]
theorem gChart_comp_fst : gChart c ιB hιB e ≫ e ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom) ≫ ιB := by
  simp [gChart, bcChart_fst]

omit [IsOpenImmersion ιB] in
@[reassoc]
theorem gChart_comp_snd : gChart c ιB hιB e ≫ e ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))) := by
  simp [gChart, bcChart_snd]

theorem opensRange_gChart :
    (gChart c ιB hιB e).opensRange = (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤) := by
  ext z
  simp only [Scheme.Hom.coe_opensRange, Set.mem_range, TopologicalSpace.Opens.map_coe, Set.mem_preimage,
    TopologicalSpace.Opens.coe_top, Scheme.Hom.coe_image, Set.image_univ]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom) t, ?_⟩
    show _ = (gChart c ιB hιB e ≫ e ≫ pullback.fst _ _) t
    rw [gChart_comp_fst]
    rfl
  · rintro ⟨w, hw⟩
    have : e z ∈ Set.range (bcChart c ιB hιB (K := K)) := by
      rw [range_bcChart]
      exact ⟨w, hw⟩
    obtain ⟨t, ht⟩ := this
    refine ⟨t, ?_⟩
    show (bcChart c ιB hιB ≫ inv e) t = z
    rw [Scheme.Hom.comp_apply, ht, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl

theorem isAffineOpen_U :
    IsAffineOpen ((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤)) := by
  rw [← opensRange_gChart c ιB hιB e]; exact isAffineOpen_opensRange _

theorem top_le_preimage_U :
    ⊤ ≤ (gChart c ιB hιB e) ⁻¹ᵁ ((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤)) := by
  rw [← opensRange_gChart c ιB hιB e, Scheme.Hom.preimage_opensRange]

noncomputable def φ : Γ(Y, (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤)) ⟶
    Γ(Spec (CommRingCat.of (K ⊗[R] B)), ⊤) :=
  (gChart c ιB hιB e).appLE _ ⊤ (top_le_preimage_U c ιB hιB e)

scoped instance φ_isIso : IsIso (φ c ιB hιB e) := by
  unfold φ
  rw [Scheme.Hom.appLE]
  have h1 : IsIso ((gChart c ιB hιB e).app
      ((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤))) :=
    Scheme.Hom.isIso_app _ _ (by rw [opensRange_gChart c ιB hιB e])
  have h2 : homOfLE (top_le_preimage_U c ιB hιB e) =
      eqToHom (by rw [← opensRange_gChart c ιB hιB e, Scheme.Hom.preimage_opensRange]) :=
    Subsingleton.elim _ _
  rw [h2, eqToHom_op]
  infer_instance

noncomputable def θ : Γ(Y, (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤)) ≅
    CommRingCat.of (K ⊗[R] B) :=
  asIso (φ c ιB hιB e) ≪≫ Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))

theorem φ_section (b : B) :
    φ c ιB hιB e (((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app (ιB ''ᵁ ⊤))
      ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) =
    (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))).inv ((1 : K) ⊗ₜ[R] b) := by
  have key : ∀ {f₁ f₂ : Spec (CommRingCat.of (K ⊗[R] B)) ⟶ X} (_ : f₁ = f₂)
      (e₁ : ⊤ ≤ f₁ ⁻¹ᵁ (ιB ''ᵁ ⊤)) (e₂ : ⊤ ≤ f₂ ⁻¹ᵁ (ιB ''ᵁ ⊤)),
      f₁.appLE (ιB ''ᵁ ⊤) ⊤ e₁ = f₂.appLE (ιB ''ᵁ ⊤) ⊤ e₂ := by
    rintro _ _ rfl _ _; rfl
  have hle : ⊤ ≤ (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom)
      ≫ ιB) ⁻¹ᵁ (ιB ''ᵁ ⊤) := by
    rw [← gChart_comp_fst c ιB hιB e]
    exact (top_le_preimage_U c ιB hιB e)
  have h1 : (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app (ιB ''ᵁ ⊤) ≫ φ c ιB hιB e =
      (ιB.appIso ⊤).hom ≫ (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom)).appTop := by
    unfold φ
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, key (gChart_comp_fst c ιB hιB e) _ hle,
      ← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ _ (ιB.preimage_image_eq ⊤).ge le_top,
      Scheme.Hom.appIso_hom', appLE_top_top]
  have h2 := congrArg (fun ψ => ψ.hom ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) h1
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [h2, Iso.inv_hom_id_apply]
  have h3 := congrArg (fun ψ => ψ.hom b) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h3
  rw [← h3]
  rfl

theorem θ_section (b : B) :
    (θ c ιB hιB e).hom (((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app (ιB ''ᵁ ⊤))
      ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) = (1 : K) ⊗ₜ[R] b := by
  simp only [θ, Iso.trans_hom, asIso_hom]
  show (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))).hom (φ c ιB hιB e _) = _
  rw [φ_section c ιB hιB e b, Iso.inv_hom_id_apply]

theorem φ_const (cK : Y ⟶ Spec (CommRingCat.of K))
    (hcK : gChart c ιB hιB e ≫ cK = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))))
    (α : K) :
    φ c ιB hιB e (Y.presheaf.map (homOfLE le_top).op (cK.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv α))) =
    (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))).inv (α ⊗ₜ[R] (1 : B)) := by
  have h1 : Y.presheaf.map (homOfLE (le_top :
      (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤) ≤ ⊤)).op ≫ φ c ιB hιB e =
      (gChart c ιB hιB e).appTop := by
    unfold φ
    rw [Scheme.Hom.map_appLE, appLE_top_top]
  have h2 := congrArg (fun ψ => ψ.hom (cK.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv α))) h1
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [h2, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hcK]
  have h3 := congrArg (fun ψ => ψ.hom α) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h3
  rw [← h3]
  rfl

theorem θ_const (cK : Y ⟶ Spec (CommRingCat.of K))
    (hcK : gChart c ιB hιB e ≫ cK = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))))
    (α : K) :
    (θ c ιB hιB e).hom (Y.presheaf.map (homOfLE le_top).op (cK.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv α))) =
    α ⊗ₜ[R] (1 : B) := by
  simp only [θ, Iso.trans_hom, asIso_hom]
  show (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))).hom (φ c ιB hιB e _) = _
  rw [φ_const c ιB hιB e cK hcK, Iso.inv_hom_id_apply]

theorem specθ_comp_fromSpec :
    Spec.map (θ c ιB hιB e).hom ≫ (isAffineOpen_U c ιB hιB e).fromSpec = gChart c ιB hιB e := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (gChart c ιB hιB e) (isAffineOpen_U c ιB hιB e)
    (isAffineOpen_top _) (top_le_preimage_U c ιB hιB e)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  simp only [θ, Iso.trans_hom, asIso_hom, Spec.map_comp, Category.assoc]
  erw [h]
  rw [← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem fromSpec_specθ (𝔮' : PrimeSpectrum (K ⊗[R] B)) :
    (isAffineOpen_U c ιB hιB e).fromSpec (Spec.map (θ c ιB hιB e).hom 𝔮') = gChart c ιB hιB e 𝔮' := by
  rw [← Scheme.Hom.comp_apply, specθ_comp_fromSpec]

theorem specθ_asIdeal (𝔮' : PrimeSpectrum (K ⊗[R] B)) :
    (Spec.map (θ c ιB hιB e).hom 𝔮').asIdeal = 𝔮'.asIdeal.comap (θ c ιB hιB e).hom.hom := rfl

end Generic

section Specific

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (B : Subalgebra (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (ιB : Spec (CommRingCat.of ↥B) ⟶ X p (ΓM M H) hj) [IsOpenImmersion ιB]
    (hιB : ιB ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥B)))

include hιB

noncomputable abbrev U₀ : 𝔛.Meta.C.Opens :=
  (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ (ιB ''ᵁ ⊤)

noncomputable abbrev g𝔛 : Spec (CommRingCat.of (AlgebraicClosure ℚ ⊗[R p] ↥B)) ⟶ 𝔛.Meta.C :=
  gChart (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta

noncomputable abbrev θ𝔛 : Γ(𝔛.Meta.C, U₀ p M H hpM hj 𝔛 B ιB) ≅ CommRingCat.of (AlgebraicClosure ℚ ⊗[R p] ↥B) :=
  θ (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta

omit [NeZero M] in
theorem g𝔛_toBase : g𝔛 p M H hpM hj 𝔛 B ιB hιB ≫ 𝔛.Meta.toBase =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := R p) (A := AlgebraicClosure ℚ) (B := ↥B))) := by
  rw [← 𝔛.heeta]; exact gChart_comp_snd (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta

noncomputable def Ψ (hne : Nonempty (Scheme.Opens.toScheme (U₀ p M H hpM hj 𝔛 B ιB))) :
    AlgebraicClosure ℚ ⊗[R p] ↥B →+* ↥(xHFunctionFieldBar M H) :=
  haveI := hne
  (𝔛.Meta.ffEquiv.symm : 𝔛.Meta.C.functionField ≃+* ↥(xHFunctionFieldBar M H)).toRingHom.comp
    ((𝔛.Meta.C.germToFunctionField (U₀ p M H hpM hj 𝔛 B ιB)).hom.comp
      (θ𝔛 p M H hpM hj 𝔛 B ιB hιB).inv.hom)

omit [NeZero M] in
theorem Ψ_apply (hne : Nonempty (Scheme.Opens.toScheme (U₀ p M H hpM hj 𝔛 B ιB))) (t : AlgebraicClosure ℚ ⊗[R p] ↥B) :
    haveI := hne
    Ψ p M H hpM hj 𝔛 B ιB hιB hne t =
      𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (U₀ p M H hpM hj 𝔛 B ιB) ((θ𝔛 p M H hpM hj 𝔛 B ιB hιB).inv t)) :=
  rfl

omit [NeZero M] in
theorem Ψ_injective (hne : Nonempty (Scheme.Opens.toScheme (U₀ p M H hpM hj 𝔛 B ιB))) :
    Function.Injective (Ψ p M H hpM hj 𝔛 B ιB hιB hne) := by
  haveI := hne
  exact dict_Ψ_injective (θ𝔛 p M H hpM hj 𝔛 B ιB hιB) 𝔛.Meta.ffEquiv.symm

omit [NeZero M] in
theorem Ψ_one_tmul (hne : Nonempty (Scheme.Opens.toScheme (U₀ p M H hpM hj 𝔛 B ιB)))
    (hMeta : ∀ b : ↥B, haveI := hne
      ((𝔛.Meta.ffEquiv.symm
        (𝔛.Meta.C.germToFunctionField (U₀ p M H hpM hj 𝔛 B ιB)
          (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
              (ιB ''ᵁ ⊤)).hom
            ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥B)).inv b))))
        : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (b : ↥B) :
    ((Ψ p M H hpM hj 𝔛 B ιB hιB hne ((1 : AlgebraicClosure ℚ) ⊗ₜ[R p] b) : ↥(xHFunctionFieldBar M H)) :
      LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) := by
  haveI := hne
  have hsec : (θ𝔛 p M H hpM hj 𝔛 B ιB hιB).inv ((1 : AlgebraicClosure ℚ) ⊗ₜ[R p] b) =
      ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app (ιB ''ᵁ ⊤))
        ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥B)).inv b)) := by
    rw [← θ_section (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta b, Iso.hom_inv_id_apply]
  rw [Ψ_apply, hsec]
  exact hMeta b

omit [NeZero M] in
theorem Ψ_tmul_one (hne : Nonempty (Scheme.Opens.toScheme (U₀ p M H hpM hj 𝔛 B ιB))) (α : AlgebraicClosure ℚ) :
    Ψ p M H hpM hj 𝔛 B ιB hιB hne (α ⊗ₜ[R p] (1 : ↥B)) =
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) α := by
  haveI := hne
  have hsec : (θ𝔛 p M H hpM hj 𝔛 B ιB hιB).inv (α ⊗ₜ[R p] (1 : ↥B)) =
      𝔛.Meta.C.presheaf.map (homOfLE le_top).op
        (𝔛.Meta.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv α)) := by
    rw [← θ_const (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta 𝔛.Meta.toBase (g𝔛_toBase p M H hpM hj 𝔛 B ιB hιB) α,
      Iso.hom_inv_id_apply]
  rw [Ψ_apply, hsec]
  apply 𝔛.Meta.ffEquiv.injective
  rw [RingEquiv.apply_symm_apply, 𝔛.Meta.ffEquiv_algebraMap]
  show (𝔛.Meta.C.presheaf.germ _ _ _) ((𝔛.Meta.C.presheaf.map (homOfLE le_top).op) _) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

omit [NeZero M] in

theorem γ_eq_Ψ_dictι
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)
    (hne : Nonempty (Scheme.Opens.toScheme (U₀ p M H hpM hj 𝔛 B ιB)))
    (hMeta : ∀ b : ↥B, haveI := hne
      ((𝔛.Meta.ffEquiv.symm
        (𝔛.Meta.C.germToFunctionField (U₀ p M H hpM hj 𝔛 B ιB)
          (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
              (ιB ''ᵁ ⊤)).hom
            ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥B)).inv b))))
        : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (γ : ↥Pl ⊗[R p] ↥B →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (α : ↥Pl) (b : ↥B), ((γ (α ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (α : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (t : ↥Pl ⊗[R p] ↥B) :
    γ t = Ψ p M H hpM hj 𝔛 B ιB hιB hne (dictι p Pl ρ hρ halg ↥B t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul π b =>
    apply Subtype.ext
    rw [hγ, dictι_tmul,
      show ((π : AlgebraicClosure ℚ) ⊗ₜ[R p] b) =
        ((π : AlgebraicClosure ℚ) ⊗ₜ[R p] (1 : ↥B)) * ((1 : AlgebraicClosure ℚ) ⊗ₜ[R p] b) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one],
      map_mul, Ψ_tmul_one]
    rw [MulMemClass.coe_mul, Ψ_one_tmul p M H hpM hj 𝔛 B ιB hιB hne hMeta b]
    show (π : AlgebraicClosure ℚ) • _ =
      ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (π : AlgebraicClosure ℚ) :
        ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * _
    rw [show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (π : AlgebraicClosure ℚ) :
        ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ) from rfl]
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

omit [NeZero M] in
theorem mem_range_stalk_iff (hne : Nonempty (Scheme.Opens.toScheme (U₀ p M H hpM hj 𝔛 B ιB)))
    (𝔮' : PrimeSpectrum (AlgebraicClosure ℚ ⊗[R p] ↥B)) (k : ↥(xHFunctionFieldBar M H)) :
    (∃ st : 𝔛.Meta.C.presheaf.stalk
        ((isAffineOpen_U (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta).fromSpec
          (Spec.map (θ𝔛 p M H hpM hj 𝔛 B ιB hιB).hom 𝔮')),
        𝔛.Meta.ffEquiv.symm (algebraMap _ 𝔛.Meta.C.functionField st) = k) ↔
    ∃ a s : AlgebraicClosure ℚ ⊗[R p] ↥B, s ∉ 𝔮'.asIdeal ∧
      k * Ψ p M H hpM hj 𝔛 B ιB hιB hne s = Ψ p M H hpM hj 𝔛 B ιB hιB hne a := by
  haveI := hne
  exact dict_mem_range_stalk_iff (isAffineOpen_U (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta)
    (θ𝔛 p M H hpM hj 𝔛 B ιB hιB) 𝔛.Meta.ffEquiv.symm 𝔮' k

omit [NeZero M] in
theorem exists_mul_Ψ_eq (hne : Nonempty (Scheme.Opens.toScheme (U₀ p M H hpM hj 𝔛 B ιB)))
    (k : ↥(xHFunctionFieldBar M H)) :
    ∃ a s : AlgebraicClosure ℚ ⊗[R p] ↥B, s ≠ 0 ∧
      k * Ψ p M H hpM hj 𝔛 B ιB hιB hne s = Ψ p M H hpM hj 𝔛 B ιB hιB hne a := by
  haveI := hne
  exact dict_exists_mul_Ψ_eq (isAffineOpen_U (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta)
    (θ𝔛 p M H hpM hj 𝔛 B ιB hιB) 𝔛.Meta.ffEquiv.symm k

omit [NeZero M] in

theorem isClosed_point (hne : Nonempty (Scheme.Opens.toScheme (U₀ p M H hpM hj 𝔛 B ιB)))
    (𝔮' : PrimeSpectrum (AlgebraicClosure ℚ ⊗[R p] ↥B)) (h𝔮' : 𝔮'.asIdeal ≠ ⊥) :
    IsClosed ({(isAffineOpen_U (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta).fromSpec
          (Spec.map (θ𝔛 p M H hpM hj 𝔛 B ιB hιB).hom 𝔮')} : Set 𝔛.Meta.C) := by
  haveI := hne
  haveI : IsDomain (AlgebraicClosure ℚ ⊗[R p] ↥B) :=
    Function.Injective.isDomain _ (Ψ_injective p M H hpM hj 𝔛 B ιB hιB hne)
  rw [fromSpec_specθ]
  apply AlgebraicCurve.isClosed_singleton_of_ne_genericPoint 𝔛.Meta.toBase
  intro hgen
  rw [← genericPoint_eq_of_isOpenImmersion (g𝔛 p M H hpM hj 𝔛 B ιB hιB)] at hgen
  have h2 := (g𝔛 p M H hpM hj 𝔛 B ιB hιB).isOpenEmbedding.injective hgen
  rw [genericPoint_eq_bot_of_affine] at h2
  exact h𝔮' (by rw [h2]; rfl)

omit [NeZero M] in

theorem exists_eval (𝔮' : PrimeSpectrum (AlgebraicClosure ℚ ⊗[R p] ↥B))
    (hx : IsClosed ({(isAffineOpen_U (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta).fromSpec
          (Spec.map (θ𝔛 p M H hpM hj 𝔛 B ιB hιB).hom 𝔮')} : Set 𝔛.Meta.C)) :
    ∃ χ' : AlgebraicClosure ℚ ⊗[R p] ↥B →+* AlgebraicClosure ℚ,
      χ'.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := AlgebraicClosure ℚ) (B := ↥B)) =
        RingHom.id _ ∧
      RingHom.ker χ' = 𝔮'.asIdeal ∧
      ((pointEquivClosedPoint 𝔛.Meta.toBase).symm ⟨_, hx⟩).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom χ') ≫
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R p) (A := AlgebraicClosure ℚ) (B := ↥B)).toRingHom) ≫ ιB := by
  set x := (isAffineOpen_U (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta).fromSpec
          (Spec.map (θ𝔛 p M H hpM hj 𝔛 B ιB hιB).hom 𝔮') with hxdef
  have hxg : x = g𝔛 p M H hpM hj 𝔛 B ιB hιB 𝔮' := fromSpec_specθ _ _ _ _ _
  set y := (pointEquivClosedPoint 𝔛.Meta.toBase).symm ⟨x, hx⟩ with hydef
  have hy1 : ∀ a, y.1 a = x := fun a => by
    rw [hydef, pointEquivClosedPoint_symm_apply_coe, pointOfClosedPoint_apply]
  have hrange : Set.range y.1 ⊆ Set.range (g𝔛 p M H hpM hj 𝔛 B ιB hιB) := by
    rintro _ ⟨a, rfl⟩
    rw [hy1, hxg]
    exact ⟨𝔮', rfl⟩
  set y₀ := IsOpenImmersion.lift (g𝔛 p M H hpM hj 𝔛 B ιB hιB) y.1 hrange with hy₀def
  have hy₀ : y₀ ≫ g𝔛 p M H hpM hj 𝔛 B ιB hιB = y.1 := IsOpenImmersion.lift_fac _ _ _
  set χc := Spec.preimage y₀ with hχcdef
  have hχc : Spec.map χc = y₀ := Spec.map_preimage _
  refine ⟨χc.hom, ?_, ?_, ?_⟩
  · have h1 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := AlgebraicClosure ℚ) (B := ↥B)) ≫ χc) = Spec.map (𝟙 _) := by
      rw [Spec.map_comp, hχc, Spec.map_id, ← g𝔛_toBase p M H hpM hj 𝔛 B ιB hιB, ← Category.assoc, hy₀]
      exact y.2
    have h2 := Spec.map_injective h1
    apply RingHom.ext
    intro a
    have h3 := congrArg (fun f => f.hom a) h2
    simpa using h3
  · have hpt : (Spec.map χc) (closedPoint (AlgebraicClosure ℚ)) = 𝔮' := by
      apply (g𝔛 p M H hpM hj 𝔛 B ιB hιB).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hχc, hy₀, hy1, hxg]
    have hbot : (closedPoint (AlgebraicClosure ℚ)).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [← hpt, RingHom.ker_eq_comap_bot, ← hbot]
    rfl
  · rw [← hy₀, Category.assoc, gChart_comp_fst, ← hχc, CommRingCat.ofHom_hom]

omit [Fact p.Prime] [NeZero M] [IsOpenImmersion ιB] hιB in

theorem transfer_frac {T T' F : Type*} [CommRing T] [CommRing T'] [CommRing F]
    (ι : T →+* T') (Ψ' : T' →+* F) (γ : T →+* F) (hγΨ : ∀ t, γ t = Ψ' (ι t))
    (c a' s' : T') (a s : T) (ha : ι a = c * a') (hs : ι s = c * s') (k : F)
    (hk : k * Ψ' s' = Ψ' a') : k * γ s = γ a := by
  rw [hγΨ, hγΨ, ha, hs, map_mul, map_mul, ← mul_assoc, mul_comm k, mul_assoc, hk]

omit [NeZero M] in

theorem mem_placeOfPoint_iff_exists_stalk
    (𝔮' : PrimeSpectrum (AlgebraicClosure ℚ ⊗[R p] ↥B))
    (hxc : IsClosed ({(isAffineOpen_U (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta).fromSpec
          (Spec.map (θ𝔛 p M H hpM hj 𝔛 B ιB hιB).hom 𝔮')} : Set 𝔛.Meta.C))
    (k : ↥(xHFunctionFieldBar M H)) :
    k ∈ (𝔛.Meta.placeOfPoint ⟨_, hxc⟩).toValuationSubring ↔
      ∃ st : 𝔛.Meta.C.presheaf.stalk
        ((isAffineOpen_U (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta).fromSpec
          (Spec.map (θ𝔛 p M H hpM hj 𝔛 B ιB hιB).hom 𝔮')),
        𝔛.Meta.ffEquiv.symm (algebraMap _ 𝔛.Meta.C.functionField st) = k := by
  have hrange := 𝔛.Meta.range_stalk_eq ⟨_, hxc⟩
  constructor
  · intro hk
    have hk2 : k ∈ (𝔛.Meta.placeOfPoint ⟨_, hxc⟩).toValuationSubring.toSubring := hk
    rw [← hrange] at hk2
    obtain ⟨st, hst⟩ := RingHom.mem_range.mp hk2
    exact ⟨st, hst⟩
  · rintro ⟨st, hst⟩
    show k ∈ (𝔛.Meta.placeOfPoint ⟨_, hxc⟩).toValuationSubring.toSubring
    rw [← hrange]
    exact RingHom.mem_range.mpr ⟨st, hst⟩

omit [NeZero M] in

theorem mem_placeOfPoint_iff
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)
    (hne : Nonempty (Scheme.Opens.toScheme (U₀ p M H hpM hj 𝔛 B ιB)))
    (γ : ↥Pl ⊗[R p] ↥B →+* ↥(xHFunctionFieldBar M H))
    (hγΨ : ∀ t, γ t = Ψ p M H hpM hj 𝔛 B ιB hιB hne (dictι p Pl ρ hρ halg ↥B t))
    (𝔮 : Ideal (↥Pl ⊗[R p] ↥B))
    (h0 : 𝔮.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥Pl) (B := ↥B)) = ⊥)
    (𝔮' : PrimeSpectrum (AlgebraicClosure ℚ ⊗[R p] ↥B))
    (hcomap : 𝔮'.asIdeal.comap (dictι p Pl ρ hρ halg ↥B).toRingHom = 𝔮)
    (hxc : IsClosed ({(isAffineOpen_U (toBase p (ΓM M H) hj) ιB hιB 𝔛.eeta).fromSpec
          (Spec.map (θ𝔛 p M H hpM hj 𝔛 B ιB hιB).hom 𝔮')} : Set 𝔛.Meta.C))
    (k : ↥(xHFunctionFieldBar M H)) :
    k ∈ (𝔛.Meta.placeOfPoint ⟨_, hxc⟩).toValuationSubring ↔
      ∃ a s : ↥Pl ⊗[R p] ↥B, s ∉ 𝔮 ∧ k * γ s = γ a := by
  refine (mem_placeOfPoint_iff_exists_stalk p M H hpM hj 𝔛 B ιB hιB 𝔮' hxc k).trans
    ((mem_range_stalk_iff p M H hpM hj 𝔛 B ιB hιB hne 𝔮' k).trans ?_)
  constructor
  · rintro ⟨a', s', hs', hk⟩
    obtain ⟨π, a, s, hπ, ha, hs⟩ := dict_exists_mul_eq p Pl ρ hρ halg ↥B a' s'
    refine ⟨a, s, ?_, ?_⟩
    · intro hsq
      have h1 : dictι p Pl ρ hρ halg ↥B s ∈ 𝔮'.asIdeal := by rw [← hcomap] at hsq; exact hsq
      rw [hs] at h1
      rcases 𝔮'.isPrime.mem_or_mem h1 with h2 | h2
      · have h3 : ((π ⊗ₜ[R p] (1 : ↥B)) : ↥Pl ⊗[R p] ↥B) ∈ 𝔮 := by
          rw [← hcomap, Ideal.mem_comap]
          show dictι p Pl ρ hρ halg ↥B (π ⊗ₜ[R p] (1 : ↥B)) ∈ 𝔮'.asIdeal
          rw [dictι_tmul]
          exact h2
        have h4 : π ∈ Ideal.comap (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := ↥Pl) (B := ↥B)) 𝔮 := h3
        rw [h0, Ideal.mem_bot] at h4
        exact hπ h4
      · exact hs' h2
    · exact transfer_frac _ _ γ hγΨ _ a' s' a s ha hs k hk
  · rintro ⟨a, s, hs, hk⟩
    refine ⟨dictι p Pl ρ hρ halg ↥B a, dictι p Pl ρ hρ halg ↥B s, ?_, ?_⟩
    · intro h
      apply hs
      rw [← hcomap, Ideal.mem_comap]
      exact h
    · rw [← hγΨ, ← hγΨ]
      exact hk

omit [NeZero M] in

theorem clause_D2
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)
    (hne : Nonempty (Scheme.Opens.toScheme (U₀ p M H hpM hj 𝔛 B ιB)))
    (γ : ↥Pl ⊗[R p] ↥B →+* ↥(xHFunctionFieldBar M H))
    (hγΨ : ∀ t, γ t = Ψ p M H hpM hj 𝔛 B ιB hιB hne (dictι p Pl ρ hρ halg ↥B t))
    (k : ↥(xHFunctionFieldBar M H)) :
    ∃ a s : ↥Pl ⊗[R p] ↥B, s ≠ 0 ∧ k * γ s = γ a := by
  obtain ⟨a', s', hs', hk⟩ := exists_mul_Ψ_eq p M H hpM hj 𝔛 B ιB hιB hne k
  obtain ⟨π, a, s, hπ, ha, hs⟩ := dict_exists_mul_eq p Pl ρ hρ halg ↥B a' s'
  have hunit : IsUnit (((π : AlgebraicClosure ℚ) ⊗ₜ[R p] (1 : ↥B))) := by
    have hπ0 : (π : AlgebraicClosure ℚ) ≠ 0 := fun h => hπ (Subtype.ext h)
    exact (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := AlgebraicClosure ℚ) (B := ↥B)).isUnit_map
      (IsUnit.mk0 _ hπ0)
  refine ⟨a, s, ?_, ?_⟩
  · intro h0
    apply hs'
    have : ((π : AlgebraicClosure ℚ) ⊗ₜ[R p] (1 : ↥B)) * s' = 0 := by rw [← hs, h0, map_zero]
    exact (hunit.mul_right_eq_zero).mp this
  · exact transfer_frac _ _ γ hγΨ _ a' s' a s ha hs k hk

omit [NeZero M] in

theorem clause_D3
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ) [Module.Flat (R p) ↥B]
    (hne : Nonempty (Scheme.Opens.toScheme (U₀ p M H hpM hj 𝔛 B ιB)))
    (γ : ↥Pl ⊗[R p] ↥B →+* ↥(xHFunctionFieldBar M H))
    (hγΨ : ∀ t, γ t = Ψ p M H hpM hj 𝔛 B ιB hιB hne (dictι p Pl ρ hρ halg ↥B t))
    (𝔮 : Ideal (↥Pl ⊗[R p] ↥B)) (h𝔮 : 𝔮.IsPrime)
    (h0 : 𝔮.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥Pl) (B := ↥B)) = ⊥)
    (hne0 : 𝔮 ≠ ⊥) :
    ∃ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (χ : ↥Pl ⊗[R p] ↥B →+* AlgebraicClosure ℚ),
      (∀ e : ↥(xHFunctionFieldBar M H),
        e ∈ (𝔛.Meta.pointEquivPlace y).toValuationSubring ↔ ∃ a s : ↥Pl ⊗[R p] ↥B, s ∉ 𝔮 ∧ e * γ s = γ a) ∧
      χ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥Pl) (B := ↥B)) = Pl.subtype ∧
      RingHom.ker χ = 𝔮 ∧
      y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom χ) ≫
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥Pl) (B := ↥B)).toRingHom) ≫
            ιB := by
  have hιinj := dict_ι_injective p Pl ρ hρ halg ↥B
  obtain ⟨𝔮'i, h𝔮', hcomap⟩ := dict_exists_isPrime_comap_eq p Pl ρ hρ halg ↥B 𝔮 h𝔮 h0
  obtain ⟨𝔮', rfl⟩ : ∃ 𝔮' : PrimeSpectrum (AlgebraicClosure ℚ ⊗[R p] ↥B), 𝔮'.asIdeal = 𝔮'i := ⟨⟨𝔮'i, h𝔮'⟩, rfl⟩
  have hP0 : 𝔮'.asIdeal ≠ ⊥ := by
    intro h
    apply hne0
    rw [← hcomap, h]
    exact Ideal.comap_bot_of_injective _ hιinj
  have hxc := isClosed_point p M H hpM hj 𝔛 B ιB hιB hne 𝔮' hP0
  obtain ⟨χ', hχ'1, hχ'2, hχ'3⟩ := exists_eval p M H hpM hj 𝔛 B ιB hιB 𝔮' hxc
  refine ⟨(pointEquivClosedPoint 𝔛.Meta.toBase).symm ⟨_, hxc⟩, χ'.comp (dictι p Pl ρ hρ halg ↥B).toRingHom,
    ?_, ?_, ?_, hχ'3.trans ?_⟩
  · intro k
    rw [CurveModel.pointEquivPlace_apply, Equiv.apply_symm_apply]
    exact mem_placeOfPoint_iff p M H hpM hj 𝔛 B ιB hιB Pl ρ hρ halg hne γ hγΨ 𝔮 h0 𝔮' hcomap hxc k
  · apply RingHom.ext
    intro π
    show χ' (dictι p Pl ρ hρ halg ↥B (π ⊗ₜ[R p] (1 : ↥B))) = (π : AlgebraicClosure ℚ)
    rw [dictι_tmul]
    exact congrArg (fun f : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ => f (π : AlgebraicClosure ℚ)) hχ'1
  · rw [← RingHom.comap_ker, hχ'2]
    exact hcomap
  · rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl

end Specific

end XLocalC4
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_and_exists_pointEquivPlace_mem_iff_of_tmul_eq_smul_coeffEmb.XLocalC4"

open XLocalC4 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)

    (B : Subalgebra (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (ιB : Spec (CommRingCat.of ↥B) ⟶ X p (ΓM M H) hj) [IsOpenImmersion ιB]
    (hιB : ιB ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥B)))

    (hne : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ (ιB ''ᵁ ⊤))))
    (hMeta : ∀ b : ↥B, haveI := hne
      ((𝔛.Meta.ffEquiv.symm
        (𝔛.Meta.C.germToFunctionField
          ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
            (ιB ''ᵁ ⊤))
          (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
              (ιB ''ᵁ ⊤)).hom
            ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥B)).inv b))))
        : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))

    (γ : ↥Pl ⊗[R p] ↥B →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (α : ↥Pl) (b : ↥B), ((γ (α ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (α : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ))) :

    Function.Injective γ ∧

    (∀ e : ↥(xHFunctionFieldBar M H), ∃ a s : ↥Pl ⊗[R p] ↥B, s ≠ 0 ∧ e * γ s = γ a) ∧

    (∀ 𝔮 : Ideal (↥Pl ⊗[R p] ↥B), 𝔮.IsPrime →
      𝔮.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥Pl) (B := ↥B)) = ⊥ → 𝔮 ≠ ⊥ →
      ∃ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (χ : ↥Pl ⊗[R p] ↥B →+* AlgebraicClosure ℚ),
        (∀ e : ↥(xHFunctionFieldBar M H),
          e ∈ (𝔛.Meta.pointEquivPlace y).toValuationSubring ↔ ∃ a s : ↥Pl ⊗[R p] ↥B, s ∉ 𝔮 ∧ e * γ s = γ a) ∧
        χ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥Pl) (B := ↥B)) = Pl.subtype ∧
        RingHom.ker χ = 𝔮 ∧
        y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥Pl) (B := ↥B)).toRingHom) ≫ ιB) := by
  haveI : Module.Flat (R p) ↥B := dict_flat p (ΓM M H) B
  have hγΨ : ∀ t, γ t = Ψ p M H hpM hj 𝔛 B ιB hιB hne (dictι p Pl ρ hρ halg ↥B t) :=
    γ_eq_Ψ_dictι p M H hpM hj 𝔛 B ιB hιB Pl ρ hρ halg hne hMeta γ hγ
  refine ⟨?_, clause_D2 p M H hpM hj 𝔛 B ιB hιB Pl ρ hρ halg hne γ hγΨ,
    clause_D3 p M H hpM hj 𝔛 B ιB hιB Pl ρ hρ halg hne γ hγΨ⟩
  intro t₁ t₂ h
  rw [hγΨ, hγΨ] at h
  exact dict_ι_injective p Pl ρ hρ halg ↥B (Ψ_injective p M H hpM hj 𝔛 B ιB hιB hne h)

end S_ModularCurve_XHDRModelAtP_injective_and_exists_pointEquivPlace_mem_iff_of_tmul_eq_smul_coeffEmb
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_injective_and_exists_pointEquivPlace_mem_iff_of_tmul_eq_smul_coeffEmb (solution)

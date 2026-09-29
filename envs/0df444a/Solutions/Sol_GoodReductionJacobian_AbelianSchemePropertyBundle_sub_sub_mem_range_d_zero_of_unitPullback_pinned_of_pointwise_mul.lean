-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.sub_sub_mem_range_d_zero_of_unitPullback_pinned_of_pointwise_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/961cd571-0d66-5f38-b275-c9a648ebfd75

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_forall_le_preimage_of_compactSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_pullback_fst_snd_of_isSeparated
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_sub_unitPullback_mem_of_d_eq_zero
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_unitPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_sub_sub_mem_range_d_zero_of_unitPullback_pinned_of_pointwise_mul
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace Ws23Cech

theorem unitPullback_sub {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z z' : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n (z - z') =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z -
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z' := by
  classical
  funext s
  rw [Pi.sub_apply]
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n _ s hinj,
      OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n _ s hinj,
      OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n _ s hinj, Pi.sub_apply]
    have e1 : (h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (z (𝒲.sortIdx 𝒦 lam s hinj) - z' (𝒲.sortIdx 𝒦 lam s hinj)) =
        (h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (z (𝒲.sortIdx 𝒦 lam s hinj)) -
          (h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (z' (𝒲.sortIdx 𝒦 lam s hinj)) := map_sub _ _ _
    rw [e1, map_sub, smul_sub]
    rfl
  · rw [OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n _ s hinj,
      OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n _ s hinj,
      OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n _ s hinj, sub_zero]

theorem unitPullback_zero {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    OModulePresheaf.unitPullback (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam n 0 = 0 := by
  have := unitPullback_sub πX πY h 𝒲 𝒦 lam hlam n 0 0
  rw [sub_self, sub_self] at this
  exact this

theorem unitPullback_mem_of_mem {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (x : (OModulePresheaf.unit πY).cochain 𝒦 n)
    (hx : x ∈ (show Submodule R ((OModulePresheaf.unit πY).cochain 𝒦 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πY).d 𝒦 m))) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n x ∈
      (show Submodule R' ((OModulePresheaf.unit πX).cochain 𝒲 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 m)) := by
  cases n with
  | zero =>
    change x ∈ (⊥ : Submodule R _) at hx
    change _ ∈ (⊥ : Submodule R' _)
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, unitPullback_zero]
  | succ m =>
    change x ∈ LinearMap.range _ at hx
    change _ ∈ LinearMap.range _
    obtain ⟨y, rfl⟩ := hx
    exact ⟨OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam m y,
      OModulePresheaf.d_unitPullback πX πY h 𝒲 𝒦 lam hlam m y⟩

theorem mem_of_unitPullback_id_mem {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    [IsSeparated π] (𝔓 𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝔓.ι) (hlam : ∀ w, 𝒲.U w ≤ (𝟙 X) ⁻¹ᵁ 𝔓.U (lam w))
    (n : ℕ) (x : (OModulePresheaf.unit π).cochain 𝔓 n) (hx : (OModulePresheaf.unit π).d 𝔓 n x = 0)
    (h : OModulePresheaf.unitPullback (πX := π) (𝟙 X) 𝒲 𝔓 lam hlam n x ∈
      (show Submodule R ((OModulePresheaf.unit π).cochain 𝒲 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit π).d 𝒲 m))) :
    x ∈ (show Submodule R ((OModulePresheaf.unit π).cochain 𝔓 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit π).d 𝔓 m)) := by
  obtain ⟨e₀, eH, he₀, heH⟩ := OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated π 𝔓 𝒲 lam hlam
  cases n with
  | zero =>
    change _ ∈ (⊥ : Submodule R _) at h
    change x ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot] at h ⊢
    have hxH : x ∈ (OModulePresheaf.unit π).H0 𝔓 := hx
    have h1 := he₀ ⟨x, hxH⟩
    rw [h] at h1
    have h2 : e₀ ⟨x, hxH⟩ = 0 := Subtype.ext h1
    have h3 : (⟨x, hxH⟩ : ↥((OModulePresheaf.unit π).H0 𝔓)) = 0 := e₀.map_eq_zero_iff.mp h2
    exact congrArg Subtype.val h3
  | succ m =>
    change _ ∈ LinearMap.range _ at h
    change x ∈ LinearMap.range _
    obtain ⟨hz, hclass⟩ := heH m ⟨x, hx⟩
    have hzero : (eH m) (Submodule.Quotient.mk ⟨x, hx⟩) = 0 := by
      rw [hclass, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact h
    have hzero' := (eH m).map_eq_zero_iff.mp hzero
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hzero'
    exact hzero'

theorem mul_val_congr' {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R g)
    {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (ht : t₁ = t₂)
    (P Q : SchemeHomOver t₁ g) (P' Q' : SchemeHomOver t₂ g) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (G.mul t₁ P Q).1 = (G.mul t₂ P' Q').1 := by
  subst ht; cases Subtype.ext hP; cases Subtype.ext hQ; rfl

end Ws23Cech

open Ws23Cech in
theorem solution
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f) (𝒦 : A.OrderedAffineCover)
    (φ ψ χ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f) (hχ : χ ≫ f = f)
    (hsum : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
        P.1 ≫ χ = (L.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩
          ⟨P.1 ≫ ψ, by rw [Category.assoc, hψ]; exact P.2⟩).1)

    (𝒱₁ : A.OrderedAffineCover) (lam₁ lam₁' : 𝒱₁.ι → 𝒦.ι)
    (hl₁ : ∀ v, 𝒱₁.U v ≤ φ ⁻¹ᵁ 𝒦.U (lam₁ v)) (hl₁' : ∀ v, 𝒱₁.U v ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam₁' v))
    (𝒱₂ : A.OrderedAffineCover) (lam₂ lam₂' : 𝒱₂.ι → 𝒦.ι)
    (hl₂ : ∀ v, 𝒱₂.U v ≤ ψ ⁻¹ᵁ 𝒦.U (lam₂ v)) (hl₂' : ∀ v, 𝒱₂.U v ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam₂' v))
    (𝒱₃ : A.OrderedAffineCover) (lam₃ lam₃' : 𝒱₃.ι → 𝒦.ι)
    (hl₃ : ∀ v, 𝒱₃.U v ≤ χ ⁻¹ᵁ 𝒦.U (lam₃ v)) (hl₃' : ∀ v, 𝒱₃.U v ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam₃' v))
    (z z₁ z₂ z₃ : (OModulePresheaf.unit f).cochain 𝒦 1)
    (hz : (OModulePresheaf.unit f).d 𝒦 1 z = 0) (hz₁ : (OModulePresheaf.unit f).d 𝒦 1 z₁ = 0)
    (hz₂ : (OModulePresheaf.unit f).d 𝒦 1 z₂ = 0) (hz₃ : (OModulePresheaf.unit f).d 𝒦 1 z₃ = 0)
    (h₁ : OModulePresheaf.unitPullback (πX := f) φ 𝒱₁ 𝒦 lam₁ hl₁ 1 z -
        OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₁ 𝒦 lam₁' hl₁' 1 z₁
      ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₁ 0))
    (h₂ : OModulePresheaf.unitPullback (πX := f) ψ 𝒱₂ 𝒦 lam₂ hl₂ 1 z -
        OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₂ 𝒦 lam₂' hl₂' 1 z₂
      ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₂ 0))
    (h₃ : OModulePresheaf.unitPullback (πX := f) χ 𝒱₃ 𝒦 lam₃ hl₃ 1 z -
        OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₃ 𝒦 lam₃' hl₃' 1 z₃
      ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₃ 0)) :
    z₃ - z₁ - z₂ ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒦 0)  := by
  classical
  haveI : IsProper f := hA.proper
  haveI : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace f

  let ℓ : A ⟶ pullback f f := pullback.lift φ ψ (hφ.trans hψ.symm)
  have hℓ1 : ℓ ≫ pullback.fst f f = φ := pullback.lift_fst _ _ _
  have hℓ2 : ℓ ≫ pullback.snd f f = ψ := pullback.lift_snd _ _ _
  have hχ' : χ = ℓ ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 := by
    have h1 := congrArg Subtype.val (L.mul_natural (pullback.fst f f ≫ f) (ℓ ≫ pullback.fst f f ≫ f) ℓ rfl
      ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
    have h2 := hsum f ⟨𝟙 A, Category.id_comp f⟩
    rw [Category.id_comp] at h2
    rw [h2]
    refine (mul_val_congr' L (by rw [← Category.assoc, hℓ1, hφ]) _ _ _ _ ?_ ?_).trans h1.symm
    · show 𝟙 A ≫ φ = ℓ ≫ pullback.fst f f
      rw [Category.id_comp, hℓ1]
    · show 𝟙 A ≫ ψ = ℓ ≫ pullback.snd f f
      rw [Category.id_comp, hℓ2]

  obtain ⟨𝒲, lw₁, lw₂, lw₃, hw₁, hw₂, hw₃⟩ :=
    Scheme.OrderedAffineCover.exists_refinement_pullback_fst_snd_of_isSeparated f 𝒦 (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1
      (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).2
  obtain ⟨b, hb⟩ := AbelianSchemePropertyBundle.exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
    k f L hA 𝒦 𝒲 lw₁ lw₂ lw₃ hw₁ hw₂ hw₃ z hz

  obtain ⟨𝒱ℓ, nl, hnl⟩ := Scheme.OrderedAffineCover.exists_forall_le_preimage_of_compactSpace
    (fun _ : Fin 1 => pullback f f) (fun _ => ℓ) (fun _ => 𝒲)
  obtain ⟨𝒱₄, nu, hnu⟩ := Scheme.OrderedAffineCover.exists_forall_le_preimage_of_compactSpace
    (fun _ : Fin 5 => A) (fun _ => 𝟙 A) ![𝒱ℓ, 𝒱₁, 𝒱₂, 𝒱₃, 𝒦]
  have hν₀ : ∀ w, 𝒱₄.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒱ℓ.U (nu 0 w) := hnu 0
  have hν₁ : ∀ w, 𝒱₄.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒱₁.U (nu 1 w) := hnu 1
  have hν₂ : ∀ w, 𝒱₄.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒱₂.U (nu 2 w) := hnu 2
  have hν₃ : ∀ w, 𝒱₄.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒱₃.U (nu 3 w) := hnu 3
  have hκ : ∀ w, 𝒱₄.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (nu 4 w) := hnu 4

  have hℓW : ∀ w, 𝒱₄.U w ≤ ℓ ⁻¹ᵁ 𝒲.U ((nl 0 ∘ nu 0) w) := fun w => (hν₀ w).trans (hnl 0 _)

  have hχW : ∀ w, 𝒱₄.U w ≤ χ ⁻¹ᵁ 𝒦.U ((lw₃ ∘ (nl 0 ∘ nu 0)) w) := fun w => by
    rw [hχ', Scheme.Hom.comp_preimage]; exact (hℓW w).trans (Scheme.Hom.preimage_mono _ (hw₃ _))
  have hφW : ∀ w, 𝒱₄.U w ≤ φ ⁻¹ᵁ 𝒦.U ((lw₁ ∘ (nl 0 ∘ nu 0)) w) := fun w => by
    rw [← hℓ1, Scheme.Hom.comp_preimage]; exact (hℓW w).trans (Scheme.Hom.preimage_mono _ (hw₁ _))
  have hψW : ∀ w, 𝒱₄.U w ≤ ψ ⁻¹ᵁ 𝒦.U ((lw₂ ∘ (nl 0 ∘ nu 0)) w) := fun w => by
    rw [← hℓ2, Scheme.Hom.comp_preimage]; exact (hℓW w).trans (Scheme.Hom.preimage_mono _ (hw₂ _))
  have hχ3 : ∀ w, 𝒱₄.U w ≤ χ ⁻¹ᵁ 𝒦.U ((lam₃ ∘ nu 3) w) := fun w => (hν₃ w).trans (hl₃ _)
  have hφ1 : ∀ w, 𝒱₄.U w ≤ φ ⁻¹ᵁ 𝒦.U ((lam₁ ∘ nu 1) w) := fun w => (hν₁ w).trans (hl₁ _)
  have hψ2 : ∀ w, 𝒱₄.U w ≤ ψ ⁻¹ᵁ 𝒦.U ((lam₂ ∘ nu 2) w) := fun w => (hν₂ w).trans (hl₂ _)
  have h13 : ∀ w, 𝒱₄.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U ((lam₃' ∘ nu 3) w) := fun w => (hν₃ w).trans (hl₃' _)
  have h11 : ∀ w, 𝒱₄.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U ((lam₁' ∘ nu 1) w) := fun w => (hν₁ w).trans (hl₁' _)
  have h12 : ∀ w, 𝒱₄.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U ((lam₂' ∘ nu 2) w) := fun w => (hν₂ w).trans (hl₂' _)

  have R0 : OModulePresheaf.unitPullback (πX := f) ℓ 𝒱₄ 𝒲 (nl 0 ∘ nu 0) hℓW 1 (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 𝒲 𝒦 lw₃ hw₃ 1 z) -
      OModulePresheaf.unitPullback (πX := f) ℓ 𝒱₄ 𝒲 (nl 0 ∘ nu 0) hℓW 1 (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lw₁ hw₁ 1 z) -
      OModulePresheaf.unitPullback (πX := f) ℓ 𝒱₄ 𝒲 (nl 0 ∘ nu 0) hℓW 1 (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lw₂ hw₂ 1 z)
      ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₄ 0) := by
    rw [← unitPullback_sub, ← unitPullback_sub, ← hb]
    exact ⟨OModulePresheaf.unitPullback (πX := f) ℓ 𝒱₄ 𝒲 (nl 0 ∘ nu 0) hℓW 0 b,
      OModulePresheaf.d_unitPullback f (pullback.fst f f ≫ f) ℓ 𝒱₄ 𝒲 (nl 0 ∘ nu 0) hℓW 0 b⟩

  have Rχ1 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f (pullback.fst f f ≫ f) f ℓ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 χ hχ'
    𝒱₄ 𝒲 𝒦 (nl 0 ∘ nu 0) lw₃ (lw₃ ∘ (nl 0 ∘ nu 0)) rfl hℓW hw₃ hχW 1 z hz
  have Rχ2 := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero f f χ 𝒱₄ 𝒦 (lw₃ ∘ (nl 0 ∘ nu 0)) (lam₃ ∘ nu 3)
    hχW hχ3 1 z hz
  have Rχ3 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f f f (𝟙 A) χ χ (Category.id_comp χ).symm
    𝒱₄ 𝒱₃ 𝒦 (nu 3) lam₃ (lam₃ ∘ nu 3) rfl hν₃ hl₃ hχ3 1 z hz
  have Rχ4 : OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₄ 𝒱₃ (nu 3) hν₃ 1 (OModulePresheaf.unitPullback (πX := f) χ 𝒱₃ 𝒦 lam₃ hl₃ 1 z) -
      OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₄ 𝒱₃ (nu 3) hν₃ 1 (OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₃ 𝒦 lam₃' hl₃' 1 z₃)
      ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₄ 0) := by
    rw [← unitPullback_sub]
    obtain ⟨c, hc⟩ := h₃
    exact ⟨OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₄ 𝒱₃ (nu 3) hν₃ 0 c, by rw [OModulePresheaf.d_unitPullback, hc]⟩
  have Rχ5 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f f f (𝟙 A) (𝟙 A) (𝟙 A) (Category.id_comp _).symm
    𝒱₄ 𝒱₃ 𝒦 (nu 3) lam₃' (lam₃' ∘ nu 3) rfl hν₃ hl₃' h13 1 z₃ hz₃
  have Rχ6 := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero f f (𝟙 A) 𝒱₄ 𝒦 (lam₃' ∘ nu 3) (nu 4)
    h13 hκ 1 z₃ hz₃

  have Rφ1 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f (pullback.fst f f ≫ f) f ℓ (pullback.fst f f) φ hℓ1.symm
    𝒱₄ 𝒲 𝒦 (nl 0 ∘ nu 0) lw₁ (lw₁ ∘ (nl 0 ∘ nu 0)) rfl hℓW hw₁ hφW 1 z hz
  have Rφ2 := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero f f φ 𝒱₄ 𝒦 (lw₁ ∘ (nl 0 ∘ nu 0)) (lam₁ ∘ nu 1)
    hφW hφ1 1 z hz
  have Rφ3 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f f f (𝟙 A) φ φ (Category.id_comp φ).symm
    𝒱₄ 𝒱₁ 𝒦 (nu 1) lam₁ (lam₁ ∘ nu 1) rfl hν₁ hl₁ hφ1 1 z hz
  have Rφ4 : OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₄ 𝒱₁ (nu 1) hν₁ 1 (OModulePresheaf.unitPullback (πX := f) φ 𝒱₁ 𝒦 lam₁ hl₁ 1 z) -
      OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₄ 𝒱₁ (nu 1) hν₁ 1 (OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₁ 𝒦 lam₁' hl₁' 1 z₁)
      ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₄ 0) := by
    rw [← unitPullback_sub]
    obtain ⟨c, hc⟩ := h₁
    exact ⟨OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₄ 𝒱₁ (nu 1) hν₁ 0 c, by rw [OModulePresheaf.d_unitPullback, hc]⟩
  have Rφ5 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f f f (𝟙 A) (𝟙 A) (𝟙 A) (Category.id_comp _).symm
    𝒱₄ 𝒱₁ 𝒦 (nu 1) lam₁' (lam₁' ∘ nu 1) rfl hν₁ hl₁' h11 1 z₁ hz₁
  have Rφ6 := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero f f (𝟙 A) 𝒱₄ 𝒦 (lam₁' ∘ nu 1) (nu 4)
    h11 hκ 1 z₁ hz₁

  have Rψ1 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f (pullback.fst f f ≫ f) f ℓ (pullback.snd f f) ψ hℓ2.symm
    𝒱₄ 𝒲 𝒦 (nl 0 ∘ nu 0) lw₂ (lw₂ ∘ (nl 0 ∘ nu 0)) rfl hℓW hw₂ hψW 1 z hz
  have Rψ2 := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero f f ψ 𝒱₄ 𝒦 (lw₂ ∘ (nl 0 ∘ nu 0)) (lam₂ ∘ nu 2)
    hψW hψ2 1 z hz
  have Rψ3 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f f f (𝟙 A) ψ ψ (Category.id_comp ψ).symm
    𝒱₄ 𝒱₂ 𝒦 (nu 2) lam₂ (lam₂ ∘ nu 2) rfl hν₂ hl₂ hψ2 1 z hz
  have Rψ4 : OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₄ 𝒱₂ (nu 2) hν₂ 1 (OModulePresheaf.unitPullback (πX := f) ψ 𝒱₂ 𝒦 lam₂ hl₂ 1 z) -
      OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₄ 𝒱₂ (nu 2) hν₂ 1 (OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₂ 𝒦 lam₂' hl₂' 1 z₂)
      ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₄ 0) := by
    rw [← unitPullback_sub]
    obtain ⟨c, hc⟩ := h₂
    exact ⟨OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₄ 𝒱₂ (nu 2) hν₂ 0 c, by rw [OModulePresheaf.d_unitPullback, hc]⟩
  have Rψ5 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f f f (𝟙 A) (𝟙 A) (𝟙 A) (Category.id_comp _).symm
    𝒱₄ 𝒱₂ 𝒦 (nu 2) lam₂' (lam₂' ∘ nu 2) rfl hν₂ hl₂' h12 1 z₂ hz₂
  have Rψ6 := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero f f (𝟙 A) 𝒱₄ 𝒦 (lam₂' ∘ nu 2) (nu 4)
    h12 hκ 1 z₂ hz₂
  change _ ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₄ 0) at Rχ1 Rχ2 Rχ3 Rχ5 Rχ6 Rφ1 Rφ2 Rφ3 Rφ5 Rφ6 Rψ1 Rψ2 Rψ3 Rψ5 Rψ6

  have hD : (OModulePresheaf.unit f).d 𝒦 1 (z₃ - z₁ - z₂) = 0 := by rw [map_sub, map_sub, hz₃, hz₁, hz₂, sub_zero, sub_zero]
  apply mem_of_unitPullback_id_mem f 𝒦 𝒱₄ (nu 4) hκ 1 (z₃ - z₁ - z₂) hD
  change _ ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₄ 0)
  rw [unitPullback_sub, unitPullback_sub]

  have key := Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.sub_mem _ R0
      (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ Rχ1 Rχ2) Rχ3) Rχ4) Rχ5) Rχ6))
      (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ Rφ1 Rφ2) Rφ3) Rφ4) Rφ5) Rφ6))
      (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ Rψ1 Rψ2) Rψ3) Rψ4) Rψ5) Rψ6))
    (Submodule.zero_mem _)
  convert key using 1
  abel

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_sub_sub_mem_range_d_zero_of_unitPullback_pinned_of_pointwise_mul
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_sub_sub_mem_range_d_zero_of_unitPullback_pinned_of_pointwise_mul (solution)

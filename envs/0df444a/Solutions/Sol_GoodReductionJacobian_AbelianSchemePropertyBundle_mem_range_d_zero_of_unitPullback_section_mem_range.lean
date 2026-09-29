-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.mem_range_d_zero_of_unitPullback_section_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/60e6c0fc-8520-5abf-8abb-8b7195866248

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_comap_id_apply
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_unitPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_specIso_inv_comp_appTop_of_isPullback
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_mem_range_d_zero_of_unitPullback_section_mem_range
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace Ws23K1

theorem unitPullback_zero {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    OModulePresheaf.unitPullback (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam n 0 = 0 := by
  classical
  funext s
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n 0 s hinj, Pi.zero_apply]
    change _ • (X.presheaf.map _).hom ((h.app _).hom (0 : Γ(Y, _))) = (0 : Γ(X, _))
    rw [map_zero, map_zero, smul_zero]
  · rw [OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n 0 s hinj]
    rfl

end Ws23K1

open Ws23K1 in
theorem solution
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (hA : AbelianSchemePropertyBundle k f)

    (e : Spec (CommRingCat.of k) ⟶ A) (he : e ≫ f = 𝟙 _)
    (s₁ s₂ : A ⟶ pullback f f)
    (hs₁ : s₁ ≫ pullback.fst f f = 𝟙 A) (hs₁' : s₁ ≫ pullback.snd f f = f ≫ e)
    (hs₂ : s₂ ≫ pullback.fst f f = f ≫ e) (hs₂' : s₂ ≫ pullback.snd f f = 𝟙 A)

    (𝒲 : (pullback f f).OrderedAffineCover) (𝒱₁ 𝒱₂ : A.OrderedAffineCover)
    (lam₁ : 𝒱₁.ι → 𝒲.ι) (lam₂ : 𝒱₂.ι → 𝒲.ι)
    (hl₁ : ∀ v, 𝒱₁.U v ≤ s₁ ⁻¹ᵁ 𝒲.U (lam₁ v)) (hl₂ : ∀ v, 𝒱₂.U v ≤ s₂ ⁻¹ᵁ 𝒲.U (lam₂ v))

    (Z : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 1)
    (hZ : (OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 1 Z = 0)
    (h₁ : OModulePresheaf.unitPullback (πX := f) s₁ 𝒱₁ 𝒲 lam₁ hl₁ 1 Z ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₁ 0))
    (h₂ : OModulePresheaf.unitPullback (πX := f) s₂ 𝒱₂ 𝒲 lam₂ hl₂ 1 Z ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₂ 0)) :
    Z ∈ LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0) := by
  classical
  haveI : IsProper f := hA.proper

  haveI hcl₁ : IsClosedImmersion s₁ := by
    have : IsClosedImmersion (s₁ ≫ pullback.fst f f) := by rw [hs₁]; infer_instance
    exact IsClosedImmersion.of_comp s₁ (pullback.fst f f)
  haveI hcl₂ : IsClosedImmersion s₂ := by
    have : IsClosedImmersion (s₂ ≫ pullback.snd f f) := by rw [hs₂']; infer_instance
    exact IsClosedImmersion.of_comp s₂ (pullback.snd f f)

  have hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom := by
    have hsq : IsPullback (𝟙 A) f f (Spec.map (CommRingCat.ofHom (RingHom.id k))) := by
      have e1 : Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _ := by
        rw [CommRingCat.ofHom_id]; exact Spec.map_id _
      rw [e1]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    exact hA.bijective_specIso_inv_comp_appTop_of_isPullback (RingHom.id k) f (𝟙 A) hsq

  have bridge : ∀ (s : A ⟶ pullback f f) [IsClosedImmersion s] (𝒱 : A.OrderedAffineCover) (lam : 𝒱.ι → 𝒲.ι)
      (hl : ∀ v, 𝒱.U v ≤ s ⁻¹ᵁ 𝒲.U (lam v)),
      OModulePresheaf.unitPullback (πX := f) s 𝒱 𝒲 lam hl 1 Z ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱 0) →
      ∃ b : (OModulePresheaf.unit f).cochain (𝒲.comap s) 0,
        (OModulePresheaf.unit f).d (𝒲.comap s) 0 b = fun t =>
          (A.presheaf.map (homOfLE (𝒲.comap_inter_le s t)).op).hom ((s.app (𝒲.inter t)).hom (Z t)) := by
    intro s _ 𝒱 lam hl hmem
    have hlamC : ∀ w : (𝒲.comap s).ι, (𝒲.comap s).U w ≤ s ⁻¹ᵁ 𝒲.U w := fun w => le_rfl

    have hr : OModulePresheaf.unitPullback (πX := f) s (𝒲.comap s) 𝒲 (fun w => w) hlamC 1 Z = fun t =>
        (A.presheaf.map (homOfLE (𝒲.comap_inter_le s t)).op).hom ((s.app (𝒲.inter t)).hom (Z t)) :=
      funext fun t => OModulePresheaf.unitPullback_comap_id_apply f (pullback.fst f f ≫ f) s 𝒲 hlamC 1 Z t

    have hdr : (OModulePresheaf.unit f).d (𝒲.comap s) 1
        (OModulePresheaf.unitPullback (πX := f) s (𝒲.comap s) 𝒲 (fun w => w) hlamC 1 Z) = 0 := by
      rw [OModulePresheaf.d_unitPullback, hZ, unitPullback_zero]

    have hl' : ∀ v, 𝒱.U v ≤ (𝟙 A) ⁻¹ᵁ (𝒲.comap s).U (lam v) := fun v => hl v

    have hcomp := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero
      f f (pullback.fst f f ≫ f) (𝟙 A) s s (Category.id_comp s).symm 𝒱 (𝒲.comap s) 𝒲 lam (fun w => w) lam rfl
      hl' hlamC hl 1 Z hZ
    change _ ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱 0) at hcomp
    have hmem' : OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 (𝒲.comap s) lam hl' 1
        (OModulePresheaf.unitPullback (πX := f) s (𝒲.comap s) 𝒲 (fun w => w) hlamC 1 Z) ∈
        LinearMap.range ((OModulePresheaf.unit f).d 𝒱 0) := by
      have := Submodule.add_mem _ hcomp hmem
      rwa [sub_add_cancel] at this

    obtain ⟨-, eH, -, heH⟩ :=
      OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated f (𝒲.comap s) 𝒱 lam hl'
    obtain ⟨hz, hclass⟩ := heH 0 ⟨_, hdr⟩
    have hzero : (eH 0) (Submodule.Quotient.mk ⟨_, hdr⟩) = 0 := by
      rw [hclass, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hmem'
    have hzero' : (Submodule.Quotient.mk ⟨_, hdr⟩ : (OModulePresheaf.unit f).HSucc (𝒲.comap s) 0) = 0 :=
      (eH 0).map_eq_zero_iff.mp hzero
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hzero'
    obtain ⟨b, hb⟩ := hzero'
    exact ⟨b, hb.trans hr⟩
  obtain hcX := bridge s₁ 𝒱₁ lam₁ hl₁ h₁
  obtain hcY := bridge s₂ 𝒱₂ lam₂ hl₂ h₂
  obtain ⟨b, hb⟩ := OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap f f hX hX e he e he
    (pullback.fst f f) (pullback.snd f f) (IsPullback.of_hasPullback f f) s₁ hs₁ hs₁' s₂ hs₂ hs₂' 𝒲 Z hZ hcX hcY
  exact ⟨b, hb⟩

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_mem_range_d_zero_of_unitPullback_section_mem_range
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_mem_range_d_zero_of_unitPullback_section_mem_range (solution)

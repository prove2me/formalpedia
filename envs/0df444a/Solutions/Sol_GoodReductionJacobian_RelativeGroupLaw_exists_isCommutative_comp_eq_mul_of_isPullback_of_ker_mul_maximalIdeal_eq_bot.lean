-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_isPullback_of_ker_mul_maximalIdeal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/86238b7f-ec2f-59cf-8a45-fc5e4669c260

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_section_comp_eq_of_isPullback_of_isNilpotent_ker
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_of_isNilpotent_ker_of_relativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_isIso_of_isPullback_of_isIso_of_isNilpotent_ker
import Theorems.Thm_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isConnected_preimage_of_isArtinianRing_of_isAlgClosed
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_isPullback_of_ker_mul_maximalIdeal_eq_bot
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.SmallExtension.pairFst_apply AlgebraicGeometry.SmallExtension.pairSnd_apply AlgebraicGeometry.SmallExtension.tensorToDualHom_tmul AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase"
p2m_attr_erase "simp" "AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelTangentPoints.const_coe AlgebraicGeometry.SquareZero.zeroSection_fst AlgebraicGeometry.SquareZero.zeroSection_snd_assoc AlgebraicGeometry.SquareZero.zeroSection_fst_assoc AlgebraicGeometry.TangentPoints.zero_coe AlgebraicGeometry.SquareZero.zeroSection_snd AlgebraicGeometry.RelTangentPoints.translate_coe Algebra.PointDerivations.map_apply_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian IsLocalRing"

universe u
open CategoryTheory.Limits

namespace K4Aux

theorem isPullback_prod {B B₀ X X₀ A A₀ : Scheme.{u}} (sπ : B₀ ⟶ B)
    (p : X ⟶ B) (p₀ : X₀ ⟶ B₀) (gX : X₀ ⟶ X) (hX : IsPullback gX p₀ p sπ)
    (f : A ⟶ B) (f₀ : A₀ ⟶ B₀) (g : A₀ ⟶ A) (hA : IsPullback g f₀ f sπ) :
    IsPullback
      (pullback.lift (pullback.fst p₀ f₀ ≫ gX) (pullback.snd p₀ f₀ ≫ g)
        (by rw [Category.assoc, Category.assoc, hX.w, hA.w, ← Category.assoc, ← Category.assoc, pullback.condition]))
      (pullback.fst p₀ f₀ ≫ p₀) (pullback.fst p f ≫ p) sπ := by
  refine IsPullback.of_isLimit' ⟨?_⟩ (PullbackCone.IsLimit.mk _ (fun s => ?_) (fun s => ?_) (fun s => ?_) (fun s l hl1 hl2 => ?_))
  · rw [← Category.assoc, pullback.lift_fst, Category.assoc, hX.w, Category.assoc]
  ·
    refine pullback.lift (hX.lift (s.fst ≫ pullback.fst p f) s.snd (by rw [Category.assoc]; exact s.condition))
      (hA.lift (s.fst ≫ pullback.snd p f) s.snd (by rw [Category.assoc, ← pullback.condition, ← Category.assoc]; exact s.condition)) ?_
    rw [hX.lift_snd, hA.lift_snd]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hX.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, hA.lift_fst]
  · show _ ≫ pullback.fst p₀ f₀ ≫ p₀ = s.snd
    rw [← Category.assoc, pullback.lift_fst, hX.lift_snd]
  · apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply hX.hom_ext
      · rw [hX.lift_fst, ← hl1, Category.assoc, Category.assoc, pullback.lift_fst]
      · rw [hX.lift_snd, ← hl2, Category.assoc]
    · rw [pullback.lift_snd]
      apply hA.hom_ext
      · rw [hA.lift_fst, ← hl1, Category.assoc, Category.assoc, pullback.lift_snd]
      · rw [hA.lift_snd, ← hl2, Category.assoc, ← pullback.condition]

end K4Aux

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π))) :
    ∃ (L : RelativeGroupLaw T' f) (_ : L.IsCommutative) (_ : AbelianSchemePropertyBundle T' f),
      ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T)) (P Q : SchemeHomOver t f₀),
        (L₀.mul t P Q).1 ≫ g =
          (L.mul (t ≫ Spec.map (CommRingCat.ofHom π))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1 := by
  classical
  haveI := hs
  haveI := hp

  obtain ⟨e, he⟩ := AlgebraicGeometry.Smooth.exists_section_comp_eq_of_isPullback_of_isNilpotent_ker T' T π hπ hker f₀ f hs g hg
    (L₀.one (𝟙 (Spec (CommRingCat.of T))))

  obtain ⟨m, hm1, hme, hm3⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot T' T π hπ hker hsmall
      f₀ L₀ hc₀ h₀ f hs hp g hg e he

  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : pullback f₀ f₀ ⟶ A₀,
      μ₀ = (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 := ⟨_, rfl⟩
  rw [← hμ₀] at hm3
  have LMUL : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t f₀),
      pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ μ₀ = (L₀.mul t x y).1 := by
    intro S t x y
    have hψ : pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ (pullback.fst f₀ f₀ ≫ f₀) = t := by
      rw [← Category.assoc, pullback.lift_fst, x.2]
    have hnat := L₀.mul_natural (pullback.fst f₀ f₀ ≫ f₀) t (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ
      ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩
    have hx : schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ
        (⟨pullback.fst f₀ f₀, rfl⟩ : SchemeHomOver (pullback.fst f₀ f₀ ≫ f₀) f₀) = x :=
      Subtype.ext (pullback.lift_fst _ _ _)
    have hy : schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ
        (⟨pullback.snd f₀ f₀, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst f₀ f₀ ≫ f₀) f₀) = y :=
      Subtype.ext (pullback.lift_snd _ _ _)
    rw [hx, hy] at hnat
    rw [hμ₀, ← hnat]
    rfl

  have hgAA := K4Aux.isPullback_prod (Spec.map (CommRingCat.ofHom π)) f f₀ g hg f f₀ g hg
  obtain ⟨gAA, hgAAdef⟩ : ∃ gAA : pullback f₀ f₀ ⟶ pullback f f,
      gAA = pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]) := ⟨_, rfl⟩
  have hgAA' : IsPullback gAA (pullback.fst f₀ f₀ ≫ f₀) (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom π)) := by
    rw [hgAAdef]; exact hgAA
  have hm3' : gAA ≫ m = μ₀ ≫ g := by rw [hgAAdef]; exact hm3
  have hgAA1 : gAA ≫ pullback.fst f f = pullback.fst f₀ f₀ ≫ g := by rw [hgAAdef, pullback.lift_fst]
  have hgAA2 : gAA ≫ pullback.snd f f = pullback.snd f₀ f₀ ≫ g := by rw [hgAAdef, pullback.lift_snd]
  have hef : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T')), (t ≫ e.1) ≫ f = t := fun t => by
    rw [Category.assoc, e.2, Category.comp_id]
  have hfe : (f ≫ e.1) ≫ f = 𝟙 A ≫ f := by rw [Category.assoc, e.2, Category.id_comp, Category.comp_id]

  obtain ⟨p1, hp1⟩ : ∃ p1 : pullback (pullback.fst f f ≫ f) f ⟶ A, p1 = pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ p2 : pullback (pullback.fst f f ≫ f) f ⟶ A, p2 = pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ p3 : pullback (pullback.fst f f ≫ f) f ⟶ A, p3 = pullback.snd (pullback.fst f f ≫ f) f := ⟨_, rfl⟩
  have c12 : p1 ≫ f = p2 ≫ f := by rw [hp1, hp2, Category.assoc, Category.assoc, pullback.condition]
  have c13 : p1 ≫ f = p3 ≫ f := by rw [hp1, hp3, Category.assoc]; exact pullback.condition
  have c23 : p2 ≫ f = p3 ≫ f := c12.symm.trans c13
  have hlm : ∀ {S : Scheme.{u}} (a b : S ⟶ A) (hab : a ≫ f = b ≫ f), (pullback.lift a b hab ≫ m) ≫ f = a ≫ f := by
    intro S a b hab; rw [Category.assoc, hm1, ← Category.assoc, pullback.lift_fst]

  have ONE_NAT : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T)),
      L₀.one t = ⟨t ≫ (L₀.one (𝟙 _)).1, by rw [Category.assoc, (L₀.one (𝟙 _)).2, Category.comp_id]⟩ := by
    intro S t

    set ε : SchemeHomOver t f₀ := ⟨t ≫ (L₀.one (𝟙 _)).1, by rw [Category.assoc, (L₀.one (𝟙 _)).2, Category.comp_id]⟩ with hε
    have hsq : (L₀.one (𝟙 _)).1 ≫ (L₀.mul f₀ ⟨𝟙 A₀, Category.id_comp _⟩ ⟨𝟙 A₀, Category.id_comp _⟩).1 = (L₀.one (𝟙 _)).1 := by
      have h := L₀.mul_natural f₀ (𝟙 _) (L₀.one (𝟙 _)).1 (L₀.one (𝟙 _)).2 ⟨𝟙 A₀, Category.id_comp _⟩ ⟨𝟙 A₀, Category.id_comp _⟩
      have h1 : schemeHomOverComp (L₀.one (𝟙 _)).1 (L₀.one (𝟙 _)).2 (⟨𝟙 A₀, Category.id_comp _⟩ : SchemeHomOver f₀ f₀) = L₀.one (𝟙 _) :=
        Subtype.ext (Category.comp_id _)
      rw [h1, L₀.one_mul] at h
      exact congrArg Subtype.val h
    have hidem : L₀.mul t ε ε = ε := by
      have h := L₀.mul_natural f₀ t (t ≫ (L₀.one (𝟙 _)).1) ε.2 ⟨𝟙 A₀, Category.id_comp _⟩ ⟨𝟙 A₀, Category.id_comp _⟩
      have h1 : schemeHomOverComp (t ≫ (L₀.one (𝟙 _)).1) ε.2 (⟨𝟙 A₀, Category.id_comp _⟩ : SchemeHomOver f₀ f₀) = ε :=
        Subtype.ext (Category.comp_id _)
      rw [h1] at h
      rw [← h]
      apply Subtype.ext
      show (t ≫ (L₀.one (𝟙 _)).1) ≫ _ = t ≫ (L₀.one (𝟙 _)).1
      rw [Category.assoc, hsq]
    calc L₀.one t = L₀.mul t (L₀.inv t ε) ε := (L₀.inv_mul_cancel t ε).symm
      _ = L₀.mul t (L₀.inv t ε) (L₀.mul t ε ε) := by rw [hidem]
      _ = L₀.mul t (L₀.mul t (L₀.inv t ε) ε) ε := (L₀.mul_assoc t _ _ _).symm
      _ = ε := by rw [L₀.inv_mul_cancel, L₀.one_mul]
  have he₀f : ((f₀ ≫ (L₀.one (𝟙 _)).1) ≫ f₀ = 𝟙 A₀ ≫ f₀) := by
    rw [Category.assoc, (L₀.one (𝟙 _)).2, Category.comp_id, Category.id_comp]
  have U2₀ : pullback.lift (f₀ ≫ (L₀.one (𝟙 _)).1) (𝟙 A₀) he₀f ≫ μ₀ = 𝟙 A₀ := by
    have := LMUL f₀ ⟨f₀ ≫ (L₀.one (𝟙 _)).1, by rw [Category.assoc, (L₀.one (𝟙 _)).2, Category.comp_id]⟩ ⟨𝟙 A₀, Category.id_comp _⟩
    have h2 : L₀.mul f₀ ⟨f₀ ≫ (L₀.one (𝟙 _)).1, by rw [Category.assoc, (L₀.one (𝟙 _)).2, Category.comp_id]⟩ ⟨𝟙 A₀, Category.id_comp _⟩ =
        ⟨𝟙 A₀, Category.id_comp _⟩ := by rw [← ONE_NAT f₀, L₀.one_mul]
    rw [h2] at this
    exact this
  have U1₀ : pullback.lift (𝟙 A₀) (f₀ ≫ (L₀.one (𝟙 _)).1) he₀f.symm ≫ μ₀ = 𝟙 A₀ := by
    have := LMUL f₀ ⟨𝟙 A₀, Category.id_comp _⟩ ⟨f₀ ≫ (L₀.one (𝟙 _)).1, by rw [Category.assoc, (L₀.one (𝟙 _)).2, Category.comp_id]⟩
    have h2 : L₀.mul f₀ ⟨𝟙 A₀, Category.id_comp _⟩ ⟨f₀ ≫ (L₀.one (𝟙 _)).1, by rw [Category.assoc, (L₀.one (𝟙 _)).2, Category.comp_id]⟩ =
        ⟨𝟙 A₀, Category.id_comp _⟩ := by rw [← ONE_NAT f₀, L₀.mul_one]
    rw [h2] at this
    exact this

  have hnil : ∀ x : PrimeSpectrum T', RingHom.ker π ≤ x.asIdeal := by
    intro x a ha
    obtain ⟨n, hn⟩ := hker
    have han : a ^ n ∈ (RingHom.ker π) ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at han
    rw [Ideal.zero_eq_bot, Ideal.mem_bot] at han
    exact x.isPrime.mem_of_pow_mem n (by rw [han]; exact x.asIdeal.zero_mem)
  have hsub : ∀ x y : PrimeSpectrum T', x = y := by
    intro x y
    have hx := IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime x.asIdeal)
    have hy := IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime y.asIdeal)
    exact PrimeSpectrum.ext (hx.trans hy.symm)
  have hsub₀ : ∀ x y : PrimeSpectrum T, x = y := by
    intro x y
    exact PrimeSpectrum.comap_injective_of_surjective π hπ (hsub _ _)
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) := IsClosedImmersion.spec_of_surjective _ hπ
  haveI hsurjπ : Surjective (Spec.map (CommRingCat.ofHom π)) := by
    refine ⟨fun x => ?_⟩
    have h1 : (1 : T') ∉ x.asIdeal := fun h => x.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    have hT : Nontrivial T := by
      refine ⟨⟨1, 0, fun h10 => h1 (hnil x ?_)⟩⟩
      rw [RingHom.mem_ker, map_one, h10]
    obtain ⟨M, hM⟩ := Ideal.exists_maximal T
    exact ⟨⟨M, hM.isPrime⟩, hsub _ _⟩
  obtain ⟨hgci, hgsurj, -, -, -⟩ :=
    AlgebraicGeometry.isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective (Spec.map (CommRingCat.ofHom π)) hg
  have hconn_f : ∀ x : ↥(Spec (CommRingCat.of T')), _root_.IsConnected (f.base ⁻¹' {x}) := by
    intro x
    obtain ⟨y, -⟩ := hsurjπ.surj x
    have hA₀ : _root_.IsConnected (Set.univ : Set ↥A₀) := by
      have := h₀.connectedFibres y
      rwa [show f₀.base ⁻¹' {y} = Set.univ from Set.eq_univ_of_forall fun a => hsub₀ _ _] at this
    have hA : _root_.IsConnected (Set.univ : Set ↥A) := by
      rw [← Set.image_univ_of_surjective hgsurj.surj]
      exact hA₀.image _ g.base.hom.continuous.continuousOn
    rwa [show f.base ⁻¹' {x} = Set.univ from Set.eq_univ_of_forall fun a => hsub _ _]
  haveI hGC : GeometricallyConnected f :=
    AlgebraicGeometry.geometricallyConnected_of_isConnected_preimage_of_isArtinianRing_of_isAlgClosed T' f hconn_f

  have hgfe : g ≫ f ≫ e.1 = (f₀ ≫ (L₀.one (𝟙 _)).1) ≫ g := by
    rw [← Category.assoc, hg.w, Category.assoc, he, Category.assoc]
  have U2 : pullback.lift (f ≫ e.1) (𝟙 A) hfe ≫ m = 𝟙 A := by
    have key := GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot T' T π hπ hker hsmall f₀ L₀ hc₀ h₀ f hs hp g hg
      f hs hp hconn_f f₀ g hg e
      ⟨pullback.lift (f ≫ e.1) (𝟙 A) hfe ≫ m, by rw [hlm, Category.assoc, e.2, Category.comp_id]⟩ ⟨𝟙 A, Category.id_comp _⟩
      (by
        show g ≫ pullback.lift (f ≫ e.1) (𝟙 A) hfe ≫ m = g ≫ 𝟙 A
        have : g ≫ pullback.lift (f ≫ e.1) (𝟙 A) hfe = pullback.lift (f₀ ≫ (L₀.one (𝟙 _)).1) (𝟙 A₀) he₀f ≫ gAA := by
          apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_fst, Category.assoc, hgAA1, pullback.lift_fst_assoc, hgfe]
          · rw [Category.assoc, pullback.lift_snd, Category.assoc, hgAA2, pullback.lift_snd_assoc,
              Category.comp_id, Category.id_comp]
        rw [← Category.assoc, this, Category.assoc, hm3', ← Category.assoc, U2₀, Category.id_comp, Category.comp_id])
      (by
        show e.1 ≫ pullback.lift (f ≫ e.1) (𝟙 A) hfe ≫ m = e.1 ≫ 𝟙 A
        have : e.1 ≫ pullback.lift (f ≫ e.1) (𝟙 A) hfe = pullback.lift e.1 e.1 rfl := by
          apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc, e.2, Category.id_comp]
          · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
        rw [← Category.assoc, this, hme, Category.comp_id])
    exact congrArg Subtype.val key
  have U1 : pullback.lift (𝟙 A) (f ≫ e.1) hfe.symm ≫ m = 𝟙 A := by
    have key := GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot T' T π hπ hker hsmall f₀ L₀ hc₀ h₀ f hs hp g hg
      f hs hp hconn_f f₀ g hg e
      ⟨pullback.lift (𝟙 A) (f ≫ e.1) hfe.symm ≫ m, by rw [hlm, Category.id_comp]⟩ ⟨𝟙 A, Category.id_comp _⟩
      (by
        show g ≫ pullback.lift (𝟙 A) (f ≫ e.1) hfe.symm ≫ m = g ≫ 𝟙 A
        have : g ≫ pullback.lift (𝟙 A) (f ≫ e.1) hfe.symm = pullback.lift (𝟙 A₀) (f₀ ≫ (L₀.one (𝟙 _)).1) he₀f.symm ≫ gAA := by
          apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_fst, Category.assoc, hgAA1, pullback.lift_fst_assoc,
              Category.comp_id, Category.id_comp]
          · rw [Category.assoc, pullback.lift_snd, Category.assoc, hgAA2, pullback.lift_snd_assoc, hgfe]
        rw [← Category.assoc, this, Category.assoc, hm3', ← Category.assoc, U1₀, Category.id_comp, Category.comp_id])
      (by
        show e.1 ≫ pullback.lift (𝟙 A) (f ≫ e.1) hfe.symm ≫ m = e.1 ≫ 𝟙 A
        have : e.1 ≫ pullback.lift (𝟙 A) (f ≫ e.1) hfe.symm = pullback.lift e.1 e.1 rfl := by
          apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
          · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, e.2, Category.id_comp]
        rw [← Category.assoc, this, hme, Category.comp_id])
    exact congrArg Subtype.val key

  haveI : GeometricallyConnected (pullback.fst f f ≫ f) := GeometricallyConnected.comp _ _
  have hconn2 : ∀ x : ↥(Spec (CommRingCat.of T')), _root_.IsConnected ((pullback.fst f f ≫ f).base ⁻¹' {x}) :=
    fun x => (pullback.fst f f ≫ f).isConnected_preimage_singleton x
  have hswap₀ : pullback.lift (pullback.snd f₀ f₀) (pullback.fst f₀ f₀) pullback.condition.symm ≫ μ₀ = μ₀ := by
    have := LMUL (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩ ⟨pullback.fst f₀ f₀, rfl⟩
    rw [hc₀.mul_comm] at this
    rw [this, hμ₀]
  have COMM : pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm ≫ m = m := by
    have key := GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot T' T π hπ hker hsmall f₀ L₀ hc₀ h₀ f hs hp g hg
      (pullback.fst f f ≫ f) inferInstance inferInstance hconn2 (pullback.fst f₀ f₀ ≫ f₀) gAA hgAA'
      ⟨pullback.lift e.1 e.1 rfl, by rw [← Category.assoc, pullback.lift_fst, e.2]⟩
      ⟨pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm ≫ m, by
        rw [hlm, pullback.condition]⟩
      ⟨m, hm1⟩
      (by
        show gAA ≫ pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm ≫ m = gAA ≫ m
        have : gAA ≫ pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm =
            pullback.lift (pullback.snd f₀ f₀) (pullback.fst f₀ f₀) pullback.condition.symm ≫ gAA := by
          apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_fst, hgAA2, Category.assoc, hgAA1, pullback.lift_fst_assoc]
          · rw [Category.assoc, pullback.lift_snd, hgAA1, Category.assoc, hgAA2, pullback.lift_snd_assoc]
        rw [← Category.assoc, this, Category.assoc, hm3', ← Category.assoc, hswap₀])
      (by
        show pullback.lift e.1 e.1 rfl ≫ pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm ≫ m =
          pullback.lift e.1 e.1 rfl ≫ m
        have : pullback.lift e.1 e.1 rfl ≫ pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm =
            pullback.lift e.1 e.1 rfl := by
          apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst]
          · rw [Category.assoc, pullback.lift_snd, pullback.lift_fst, pullback.lift_snd]
        rw [← Category.assoc, this])
    exact congrArg Subtype.val key

  haveI : GeometricallyConnected (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) := GeometricallyConnected.comp _ _
  have hconn3 : ∀ x : ↥(Spec (CommRingCat.of T')),
      _root_.IsConnected ((pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)).base ⁻¹' {x}) :=
    fun x => (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)).isConnected_preimage_singleton x
  have hg3P := K4Aux.isPullback_prod (Spec.map (CommRingCat.ofHom π)) (pullback.fst f f ≫ f) (pullback.fst f₀ f₀ ≫ f₀) gAA hgAA' f f₀ g hg
  obtain ⟨g3, hg3def⟩ : ∃ g3 : pullback (pullback.fst f₀ f₀ ≫ f₀) f₀ ⟶ pullback (pullback.fst f f ≫ f) f,
      g3 = pullback.lift (pullback.fst (pullback.fst f₀ f₀ ≫ f₀) f₀ ≫ gAA) (pullback.snd (pullback.fst f₀ f₀ ≫ f₀) f₀ ≫ g)
        (by rw [Category.assoc, Category.assoc, hgAA'.w, hg.w, ← Category.assoc,
              pullback.condition (f := pullback.fst f₀ f₀ ≫ f₀) (g := f₀), Category.assoc]) := ⟨_, rfl⟩
  have hg3' : IsPullback g3 (pullback.fst (pullback.fst f₀ f₀ ≫ f₀) f₀ ≫ (pullback.fst f₀ f₀ ≫ f₀))
      (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) (Spec.map (CommRingCat.ofHom π)) := by
    rw [hg3def]; exact hg3P

  obtain ⟨q1, hq1⟩ : ∃ q1 : pullback (pullback.fst f₀ f₀ ≫ f₀) f₀ ⟶ A₀, q1 = pullback.fst (pullback.fst f₀ f₀ ≫ f₀) f₀ ≫ pullback.fst f₀ f₀ := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q2 : pullback (pullback.fst f₀ f₀ ≫ f₀) f₀ ⟶ A₀, q2 = pullback.fst (pullback.fst f₀ f₀ ≫ f₀) f₀ ≫ pullback.snd f₀ f₀ := ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ q3 : pullback (pullback.fst f₀ f₀ ≫ f₀) f₀ ⟶ A₀, q3 = pullback.snd (pullback.fst f₀ f₀ ≫ f₀) f₀ := ⟨_, rfl⟩
  have d12 : q1 ≫ f₀ = q2 ≫ f₀ := by rw [hq1, hq2, Category.assoc, Category.assoc, pullback.condition]
  have d13 : q1 ≫ f₀ = q3 ≫ f₀ := by rw [hq1, hq3, Category.assoc]; exact pullback.condition
  have hg3p1 : g3 ≫ p1 = q1 ≫ g := by rw [hp1, hq1, hg3def, pullback.lift_fst_assoc, Category.assoc, hgAA1, Category.assoc]
  have hg3p2 : g3 ≫ p2 = q2 ≫ g := by rw [hp2, hq2, hg3def, pullback.lift_fst_assoc, Category.assoc, hgAA2, Category.assoc]
  have hg3p3 : g3 ≫ p3 = q3 ≫ g := by rw [hp3, hq3, hg3def, pullback.lift_snd]

  have LMUL' : ∀ (a b : pullback (pullback.fst f₀ f₀ ≫ f₀) f₀ ⟶ A₀) (ha : a ≫ f₀ = q1 ≫ f₀) (hb : b ≫ f₀ = q1 ≫ f₀),
      pullback.lift (a ≫ g) (b ≫ g) (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, ha, hb]) ≫ m =
        (L₀.mul (q1 ≫ f₀) ⟨a, ha⟩ ⟨b, hb⟩).1 ≫ g := by
    intro a b ha hb
    have : pullback.lift (a ≫ g) (b ≫ g) (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, ha, hb]) =
        pullback.lift a b (ha.trans hb.symm) ≫ gAA := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, hgAA1, pullback.lift_fst_assoc]
      · rw [pullback.lift_snd, Category.assoc, hgAA2, pullback.lift_snd_assoc]
    rw [this, Category.assoc, hm3', ← Category.assoc, LMUL (q1 ≫ f₀) ⟨a, ha⟩ ⟨b, hb⟩]
  have hs3 : pullback.lift e.1 e.1 rfl ≫ (pullback.fst f f ≫ f) = e.1 ≫ f := by rw [← Category.assoc, pullback.lift_fst]
  have ASSOC : pullback.lift (pullback.lift p1 p2 c12 ≫ m) p3 ((hlm p1 p2 c12).trans c13) ≫ m =
      pullback.lift p1 (pullback.lift p2 p3 c23 ≫ m) (c12.trans (hlm p2 p3 c23).symm) ≫ m := by
    have hu : (pullback.lift (pullback.lift p1 p2 c12 ≫ m) p3 ((hlm p1 p2 c12).trans c13) ≫ m) ≫ f =
        pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f) := by
      rw [hlm, hlm, hp1, Category.assoc]
    have hv : (pullback.lift p1 (pullback.lift p2 p3 c23 ≫ m) (c12.trans (hlm p2 p3 c23).symm) ≫ m) ≫ f =
        pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f) := by
      rw [hlm, hp1, Category.assoc]

    have hmulg : ∀ (x : SchemeHomOver (q1 ≫ f₀) f₀), (x.1 ≫ g) ≫ f = q1 ≫ f₀ ≫ Spec.map (CommRingCat.ofHom π) := by
      intro x; rw [Category.assoc, hg.w, ← Category.assoc, x.2, Category.assoc]
    have hredU : g3 ≫ (pullback.lift (pullback.lift p1 p2 c12 ≫ m) p3 ((hlm p1 p2 c12).trans c13) ≫ m) =
        (L₀.mul (q1 ≫ f₀) (L₀.mul (q1 ≫ f₀) ⟨q1, rfl⟩ ⟨q2, d12.symm⟩) ⟨q3, d13.symm⟩).1 ≫ g := by
      have h1 : g3 ≫ pullback.lift p1 p2 c12 ≫ m = (L₀.mul (q1 ≫ f₀) ⟨q1, rfl⟩ ⟨q2, d12.symm⟩).1 ≫ g := by
        rw [← Category.assoc]
        have : g3 ≫ pullback.lift p1 p2 c12 = pullback.lift (q1 ≫ g) (q2 ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, d12]) := by
          apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hg3p1]
          · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hg3p2]
        rw [this]
        exact LMUL' q1 q2 rfl d12.symm
      rw [← Category.assoc]
      have : g3 ≫ pullback.lift (pullback.lift p1 p2 c12 ≫ m) p3 ((hlm p1 p2 c12).trans c13) =
          pullback.lift ((L₀.mul (q1 ≫ f₀) ⟨q1, rfl⟩ ⟨q2, d12.symm⟩).1 ≫ g) (q3 ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc,
                  (L₀.mul (q1 ≫ f₀) ⟨q1, rfl⟩ ⟨q2, d12.symm⟩).2, d13]) := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]; exact h1
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hg3p3]
      rw [this]
      exact LMUL' _ q3 (L₀.mul (q1 ≫ f₀) ⟨q1, rfl⟩ ⟨q2, d12.symm⟩).2 d13.symm
    have hredV : g3 ≫ (pullback.lift p1 (pullback.lift p2 p3 c23 ≫ m) (c12.trans (hlm p2 p3 c23).symm) ≫ m) =
        (L₀.mul (q1 ≫ f₀) ⟨q1, rfl⟩ (L₀.mul (q1 ≫ f₀) ⟨q2, d12.symm⟩ ⟨q3, d13.symm⟩)).1 ≫ g := by
      have h1 : g3 ≫ pullback.lift p2 p3 c23 ≫ m = (L₀.mul (q1 ≫ f₀) ⟨q2, d12.symm⟩ ⟨q3, d13.symm⟩).1 ≫ g := by
        rw [← Category.assoc]
        have : g3 ≫ pullback.lift p2 p3 c23 = pullback.lift (q2 ≫ g) (q3 ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, ← d12, d13]) := by
          apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hg3p2]
          · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hg3p3]
        rw [this]
        exact LMUL' q2 q3 d12.symm d13.symm
      rw [← Category.assoc]
      have : g3 ≫ pullback.lift p1 (pullback.lift p2 p3 c23 ≫ m) (c12.trans (hlm p2 p3 c23).symm) =
          pullback.lift (q1 ≫ g) ((L₀.mul (q1 ≫ f₀) ⟨q2, d12.symm⟩ ⟨q3, d13.symm⟩).1 ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc,
                  (L₀.mul (q1 ≫ f₀) ⟨q2, d12.symm⟩ ⟨q3, d13.symm⟩).2]) := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hg3p1]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]; exact h1
      rw [this]
      exact LMUL' q1 _ rfl (L₀.mul (q1 ≫ f₀) ⟨q2, d12.symm⟩ ⟨q3, d13.symm⟩).2

    have hsp1 : pullback.lift (pullback.lift e.1 e.1 rfl) e.1 hs3 ≫ p1 = e.1 := by rw [hp1, pullback.lift_fst_assoc, pullback.lift_fst]
    have hsp2 : pullback.lift (pullback.lift e.1 e.1 rfl) e.1 hs3 ≫ p2 = e.1 := by rw [hp2, pullback.lift_fst_assoc, pullback.lift_snd]
    have hsp3 : pullback.lift (pullback.lift e.1 e.1 rfl) e.1 hs3 ≫ p3 = e.1 := by rw [hp3, pullback.lift_snd]
    have hsecU : pullback.lift (pullback.lift e.1 e.1 rfl) e.1 hs3 ≫
        (pullback.lift (pullback.lift p1 p2 c12 ≫ m) p3 ((hlm p1 p2 c12).trans c13) ≫ m) = e.1 := by
      rw [← Category.assoc]
      have : pullback.lift (pullback.lift e.1 e.1 rfl) e.1 hs3 ≫ pullback.lift (pullback.lift p1 p2 c12 ≫ m) p3 ((hlm p1 p2 c12).trans c13) =
          pullback.lift e.1 e.1 rfl := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc]
          have : pullback.lift (pullback.lift e.1 e.1 rfl) e.1 hs3 ≫ pullback.lift p1 p2 c12 = pullback.lift e.1 e.1 rfl := by
            apply pullback.hom_ext
            · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hsp1]
            · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hsp2]
          rw [this, hme]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hsp3]
      rw [this, hme]
    have hsecV : pullback.lift (pullback.lift e.1 e.1 rfl) e.1 hs3 ≫
        (pullback.lift p1 (pullback.lift p2 p3 c23 ≫ m) (c12.trans (hlm p2 p3 c23).symm) ≫ m) = e.1 := by
      rw [← Category.assoc]
      have : pullback.lift (pullback.lift e.1 e.1 rfl) e.1 hs3 ≫ pullback.lift p1 (pullback.lift p2 p3 c23 ≫ m) (c12.trans (hlm p2 p3 c23).symm) =
          pullback.lift e.1 e.1 rfl := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hsp1]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc]
          have : pullback.lift (pullback.lift e.1 e.1 rfl) e.1 hs3 ≫ pullback.lift p2 p3 c23 = pullback.lift e.1 e.1 rfl := by
            apply pullback.hom_ext
            · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hsp2]
            · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hsp3]
          rw [this, hme]
      rw [this, hme]
    have key := GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot T' T π hπ hker hsmall f₀ L₀ hc₀ h₀ f hs hp g hg
      (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) inferInstance inferInstance hconn3
      (pullback.fst (pullback.fst f₀ f₀ ≫ f₀) f₀ ≫ (pullback.fst f₀ f₀ ≫ f₀)) g3 hg3'
      ⟨pullback.lift (pullback.lift e.1 e.1 rfl) e.1 hs3, by
        rw [← Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, e.2]⟩
      ⟨_, hu⟩ ⟨_, hv⟩
      (by
        show g3 ≫ _ = g3 ≫ _
        rw [hredU, hredV, L₀.mul_assoc])
      (by
        show pullback.lift (pullback.lift e.1 e.1 rfl) e.1 hs3 ≫ _ = pullback.lift (pullback.lift e.1 e.1 rfl) e.1 hs3 ≫ _
        rw [hsecU, hsecV])
    exact congrArg Subtype.val key

  obtain ⟨sh, hshdef⟩ : ∃ sh : pullback f f ⟶ pullback f f, sh = pullback.lift (pullback.fst f f) m hm1.symm := ⟨_, rfl⟩
  have hshIso : IsIso sh := by

    have RINV₀ : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T)) (x : SchemeHomOver t f₀),
        L₀.mul t x (L₀.inv t x) = L₀.one t := by
      intro S t x
      have h1 : L₀.mul t (L₀.inv t x) (L₀.mul t x (L₀.inv t x)) = L₀.inv t x := by
        rw [← L₀.mul_assoc, L₀.inv_mul_cancel, L₀.one_mul]
      have h2 := congrArg (fun z => L₀.mul t (L₀.inv t (L₀.inv t x)) z) h1
      try simp only at h2
      rw [← L₀.mul_assoc, L₀.inv_mul_cancel, L₀.one_mul] at h2
      exact h2
    have LUNIQ : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T)) (a b : SchemeHomOver t f₀),
        L₀.mul t a b = L₀.one t → a = L₀.inv t b := by
      intro S t a b hab
      calc a = L₀.mul t a (L₀.one t) := (L₀.mul_one t a).symm
        _ = L₀.mul t a (L₀.mul t b (L₀.inv t b)) := by rw [RINV₀]
        _ = L₀.mul t (L₀.mul t a b) (L₀.inv t b) := (L₀.mul_assoc t _ _ _).symm
        _ = L₀.inv t b := by rw [hab, L₀.one_mul]
    have INV_NAT : ∀ {S S' : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T)) (t' : S' ⟶ Spec (CommRingCat.of T))
        (ψ : S' ⟶ S) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f₀),
        schemeHomOverComp ψ hψ (L₀.inv t x) = L₀.inv t' (schemeHomOverComp ψ hψ x) := by
      intro S S' t t' ψ hψ x
      apply LUNIQ
      rw [← L₀.mul_natural, L₀.inv_mul_cancel, ONE_NAT t, ONE_NAT t']
      apply Subtype.ext
      show ψ ≫ t ≫ _ = t' ≫ _
      rw [← Category.assoc, hψ]

    have hμf : pullback.fst f₀ f₀ ≫ f₀ = μ₀ ≫ f₀ := by
      rw [hμ₀]; exact (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).2.symm
    obtain ⟨sh₀, hsh₀def⟩ : ∃ sh₀ : pullback f₀ f₀ ⟶ pullback f₀ f₀, sh₀ = pullback.lift (pullback.fst f₀ f₀) μ₀ hμf := ⟨_, rfl⟩
    have hsh₀1 : sh₀ ≫ pullback.fst f₀ f₀ = pullback.fst f₀ f₀ := by rw [hsh₀def, pullback.lift_fst]
    have hsh₀2 : sh₀ ≫ pullback.snd f₀ f₀ = μ₀ := by rw [hsh₀def, pullback.lift_snd]
    haveI : IsIso sh₀ := by
      set t₀ := pullback.fst f₀ f₀ ≫ f₀ with ht₀
      set X : SchemeHomOver t₀ f₀ := ⟨pullback.fst f₀ f₀, rfl⟩ with hX
      set Y : SchemeHomOver t₀ f₀ := ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩ with hY
      have hμXY : (L₀.mul t₀ X Y).1 = μ₀ := by rw [hμ₀]
      refine ⟨⟨pullback.lift (pullback.fst f₀ f₀) (L₀.mul t₀ (L₀.inv t₀ X) Y).1 (L₀.mul t₀ (L₀.inv t₀ X) Y).2.symm, ?_, ?_⟩⟩
      · apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, hsh₀1, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
          have hψ : sh₀ ≫ t₀ = t₀ := by rw [ht₀, ← Category.assoc, hsh₀1]
          have hnat := L₀.mul_natural t₀ t₀ sh₀ hψ (L₀.inv t₀ X) Y
          have hcY : schemeHomOverComp sh₀ hψ Y = L₀.mul t₀ X Y := Subtype.ext (by rw [schemeHomOverComp_coe, hsh₀2, hμXY])
          have hcX : schemeHomOverComp sh₀ hψ X = X := Subtype.ext hsh₀1
          rw [INV_NAT t₀ t₀ sh₀ hψ X, hcX, hcY, ← L₀.mul_assoc, L₀.inv_mul_cancel, L₀.one_mul] at hnat
          exact (congrArg Subtype.val hnat).trans rfl
      · apply pullback.hom_ext
        · rw [Category.assoc, hsh₀1, pullback.lift_fst, Category.id_comp]
        · rw [Category.assoc, hsh₀2, Category.id_comp]
          have := LMUL t₀ X (L₀.mul t₀ (L₀.inv t₀ X) Y)
          rw [← L₀.mul_assoc, RINV₀, L₀.one_mul] at this
          exact this

    have hφ₀ : sh₀ ≫ gAA = gAA ≫ sh := by
      apply pullback.hom_ext
      · rw [Category.assoc, hgAA1, ← Category.assoc, hsh₀1, Category.assoc, hshdef, pullback.lift_fst, hgAA1]
      · rw [Category.assoc, hgAA2, ← Category.assoc, hsh₀2, Category.assoc, hshdef, pullback.lift_snd, hm3']
    have hφ₀q : sh₀ ≫ (pullback.fst f₀ f₀ ≫ f₀) = pullback.fst f₀ f₀ ≫ f₀ := by rw [← Category.assoc, hsh₀1]
    have hshq : sh ≫ (pullback.fst f f ≫ f) = pullback.fst f f ≫ f := by rw [← Category.assoc, hshdef, pullback.lift_fst]
    exact AlgebraicGeometry.isIso_of_isPullback_of_isIso_of_isNilpotent_ker T' T π hπ hker (pullback.fst f f ≫ f) (pullback.fst f f ≫ f) sh hshq
      (pullback.fst f₀ f₀ ≫ f₀) (pullback.fst f₀ f₀ ≫ f₀) gAA hgAA' gAA hgAA' sh₀ hφ₀ hφ₀q
  obtain ⟨ι, hιdef⟩ : ∃ ι : A ⟶ A, ι = (pullback.lift (𝟙 A) (f ≫ e.1)
      hfe.symm ≫ inv sh) ≫ pullback.snd f f := ⟨_, rfl⟩
  have hιf : ι ≫ f = f := by
    rw [hιdef, Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc (inv sh)]
    have : inv sh ≫ pullback.fst f f = pullback.fst f f := by
      rw [IsIso.inv_comp_eq, hshdef, pullback.lift_fst]
    rw [this, ← Category.assoc, pullback.lift_fst, Category.id_comp]
  have RINV : pullback.lift (𝟙 A) ι (by rw [hιf, Category.id_comp]) ≫ m = f ≫ e.1 := by
    have h1 : (pullback.lift (𝟙 A) (f ≫ e.1) hfe.symm ≫ inv sh) ≫ sh =
        pullback.lift (𝟙 A) (f ≫ e.1) hfe.symm := by
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have h2 : pullback.lift (𝟙 A) ι (by rw [hιf, Category.id_comp]) =
        pullback.lift (𝟙 A) (f ≫ e.1) hfe.symm ≫ inv sh := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc]
        have : inv sh ≫ pullback.fst f f = pullback.fst f f := by rw [IsIso.inv_comp_eq, hshdef, pullback.lift_fst]
        rw [this, pullback.lift_fst]
      · rw [pullback.lift_snd, hιdef, Category.assoc]
    rw [h2]
    have h3 : sh ≫ pullback.snd f f = m := by rw [hshdef, pullback.lift_snd]
    rw [← h3, ← Category.assoc, h1, pullback.lift_snd]
  have LINV : pullback.lift ι (𝟙 A) (by rw [hιf, Category.id_comp]) ≫ m = f ≫ e.1 := by
    rw [← COMM, ← Category.assoc]
    have : pullback.lift ι (𝟙 A) (by rw [hιf, Category.id_comp]) ≫ pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm =
        pullback.lift (𝟙 A) ι (by rw [hιf, Category.id_comp]) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_fst, pullback.lift_snd]
    rw [this, RINV]

  let L : RelativeGroupLaw T' f :=
    { mul := fun t P Q => ⟨pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ m, by
        rw [Category.assoc, hm1, ← Category.assoc, pullback.lift_fst, P.2]⟩
      one := fun t => ⟨t ≫ e.1, by rw [Category.assoc, e.2, Category.comp_id]⟩
      inv := fun t P => ⟨P.1 ≫ ι, by rw [Category.assoc, hιf, P.2]⟩
      mul_assoc := by
        intro S t x y z
        apply Subtype.ext
        show pullback.lift (pullback.lift x.1 y.1 _ ≫ m) z.1 _ ≫ m = pullback.lift x.1 (pullback.lift y.1 z.1 _ ≫ m) _ ≫ m
        have hw : pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ (pullback.fst f f ≫ f) = z.1 ≫ f := by
          rw [← Category.assoc, pullback.lift_fst, x.2, z.2]
        have hw1 : pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) z.1 hw ≫ p1 = x.1 := by
          rw [hp1, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
        have hw2 : pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) z.1 hw ≫ p2 = y.1 := by
          rw [hp2, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]
        have hw3 : pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) z.1 hw ≫ p3 = z.1 := by
          rw [hp3, pullback.lift_snd]
        have := congrArg (fun φ => pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) z.1 hw ≫ φ) ASSOC
        simp only [← Category.assoc] at this
        convert this using 2
        · apply pullback.hom_ext
          · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc]
            congr 1
            apply pullback.hom_ext
            · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, hw1]
            · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, hw2]
          · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, hw3]
        · apply pullback.hom_ext
          · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, hw1]
          · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc]
            congr 1
            apply pullback.hom_ext
            · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, hw2]
            · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, hw3]
      one_mul := by
        intro S t x
        apply Subtype.ext
        show pullback.lift (t ≫ e.1) x.1 _ ≫ m = x.1
        have : pullback.lift (t ≫ e.1) x.1 ((hef t).trans x.2.symm) =
            x.1 ≫ pullback.lift (f ≫ e.1) (𝟙 A) hfe := by
          apply pullback.hom_ext
          · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, x.2]
          · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
        rw [this, Category.assoc, U2, Category.comp_id]
      mul_one := by
        intro S t x
        apply Subtype.ext
        show pullback.lift x.1 (t ≫ e.1) _ ≫ m = x.1
        have : pullback.lift x.1 (t ≫ e.1) (x.2.trans (hef t).symm) =
            x.1 ≫ pullback.lift (𝟙 A) (f ≫ e.1) hfe.symm := by
          apply pullback.hom_ext
          · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id]
          · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, x.2]
        rw [this, Category.assoc, U1, Category.comp_id]
      inv_mul_cancel := by
        intro S t x
        apply Subtype.ext
        show pullback.lift (x.1 ≫ ι) x.1 _ ≫ m = t ≫ e.1
        have hxι : (x.1 ≫ ι) ≫ f = t := by rw [Category.assoc, hιf, x.2]
        have : pullback.lift (x.1 ≫ ι) x.1 (hxι.trans x.2.symm) =
            x.1 ≫ pullback.lift ι (𝟙 A) (by rw [hιf, Category.id_comp]) := by
          apply pullback.hom_ext
          · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
          · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
        rw [this, Category.assoc, LINV, ← Category.assoc, x.2]
      mul_natural := by
        intro S S' t t' ψ hψ x y
        apply Subtype.ext
        show ψ ≫ (pullback.lift x.1 y.1 _ ≫ m) = pullback.lift (ψ ≫ x.1) (ψ ≫ y.1) _ ≫ m
        rw [← Category.assoc]
        congr 1
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd] }
  have hLc : L.IsCommutative := by
    intro S t x y
    apply Subtype.ext
    show pullback.lift x.1 y.1 _ ≫ m = pullback.lift y.1 x.1 _ ≫ m
    conv_lhs => rw [← COMM]
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_fst, pullback.lift_snd]
  have hbundle : AbelianSchemePropertyBundle T' f :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback_of_isNilpotent_ker_of_relativeGroupLaw T' T π hπ hker
      f₀ h₀ f hs hp g hg L
  refine ⟨L, hLc, hbundle, ?_⟩
  intro S t P Q
  show (L₀.mul t P Q).1 ≫ g = pullback.lift (P.1 ≫ g) (Q.1 ≫ g) _ ≫ m
  have : pullback.lift (P.1 ≫ g) (Q.1 ≫ g)
        ((by rw [Category.assoc, hg.w, ← Category.assoc, P.2] : (P.1 ≫ g) ≫ f = t ≫ Spec.map (CommRingCat.ofHom π)).trans
          ((by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]) : (Q.1 ≫ g) ≫ f = t ≫ Spec.map (CommRingCat.ofHom π)).symm) =
      pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ gAA := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hgAA1, ← Category.assoc, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, hgAA2, ← Category.assoc, pullback.lift_snd]
  rw [this, Category.assoc, hm3', ← Category.assoc, LMUL]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_isPullback_of_ker_mul_maximalIdeal_eq_bot
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_isPullback_of_ker_mul_maximalIdeal_eq_bot (solution)

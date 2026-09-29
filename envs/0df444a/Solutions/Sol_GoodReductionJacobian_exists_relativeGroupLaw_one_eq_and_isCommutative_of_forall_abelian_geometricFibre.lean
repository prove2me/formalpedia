-- Prove2me | solution 1 for GoodReductionJacobian.exists_relativeGroupLaw_one_eq_and_isCommutative_of_forall_abelian_geometricFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/dd18428f-ff31-5789-b99a-86db43579336

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_Subalgebra_exists_fg_le_forall_comap_inclusion_mem_of_isOpen
import Theorems.Thm_GoodReductionJacobian_smooth_and_isConnected_preimage_and_abelianSchemePropertyBundle_of_forall_geometricFibre
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isOpen_setOf_abelian_geometricFibre_and_preimage_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map
import Theorems.Thm_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_and_isCommutative_of_smooth_of_isClosedImmersion_proj_of_isNoetherianRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_comp_eq_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_one_eq_of_abelianSchemePropertyBundle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_and_isCommutative_of_forall_abelian_geometricFibre
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.isClosedImmersion_adicThickeningι AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.adicThickeningTransition_ι AlgebraicGeometry.SmallExtension.pairFst_apply AlgebraicGeometry.SmallExtension.pairSnd_apply AlgebraicGeometry.SmallExtension.tensorToDualHom_tmul AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelTangentPoints.const_coe AlgebraicGeometry.SquareZero.zeroSection_fst AlgebraicGeometry.SquareZero.zeroSection_snd_assoc AlgebraicGeometry.SquareZero.zeroSection_fst_assoc AlgebraicGeometry.TangentPoints.zero_coe AlgebraicGeometry.SquareZero.zeroSection_snd AlgebraicGeometry.RelTangentPoints.translate_coe Algebra.PointDerivations.map_apply_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app"

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type} [CommRing R] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R N = f)
    (g : ℕ) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hab : ∀ (s : ↥(Spec (CommRingCat.of R))) (k : Type) [Field k] [IsAlgClosed k] (x : R →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g ∧
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))) :
    ∃ L : RelativeGroupLaw R f, L.one (𝟙 _) = ε ∧ L.IsCommutative ∧
      ∀ L' : RelativeGroupLaw R f, L'.one (𝟙 _) = ε → L' = L := by
  classical

  obtain ⟨hsm, hconnR, hgeoR, -⟩ :=
    GoodReductionJacobian.smooth_and_isConnected_preimage_and_abelianSchemePropertyBundle_of_forall_geometricFibre f g hab

  obtain ⟨S₀, hS₀fg, Z₀, f₀, gg, hpb, hsm₀, hpr₀, ⟨N₀, ι₀, hι₀, hι₀f⟩, -, ε₀, hε₀⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj f hsm inferInstance hproj
      (fun k _ _ x => hgeoR k x) ε
  haveI : Smooth f₀ := hsm₀
  haveI : IsProper f₀ := hpr₀
  haveI : IsClosedImmersion ι₀ := hι₀

  obtain ⟨hU₀, hU₀bc⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_abelian_geometricFibre_and_preimage_eq_of_isPullback
      f₀ ⟨N₀, ι₀, hι₀, hι₀f⟩ g ε₀
  have hlocR := hU₀bc R (algebraMap ↥S₀ R) Z f gg hpb

  obtain ⟨S₁, h01, hS₁fg, hS₁U⟩ :=
    Subalgebra.exists_fg_le_forall_comap_inclusion_mem_of_isOpen S₀ hS₀fg _ hU₀ (fun p => by
      have hp := (Set.ext_iff.mp hlocR p).mp (hab p)
      exact hp)
  letI alg01 : Algebra ↥S₀ ↥S₁ := (Subalgebra.inclusion h01).toRingHom.toAlgebra
  have halg01 : algebraMap ↥S₀ ↥S₁ = (Subalgebra.inclusion h01).toRingHom := rfl
  have hcomp : (algebraMap ↥S₁ R).comp (algebraMap ↥S₀ ↥S₁) = algebraMap ↥S₀ R := RingHom.ext fun _ => rfl
  have hbb : Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ R)) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R)) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ ↥S₁)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  haveI : Algebra.FiniteType ℤ ↥S₁ := (Subalgebra.fg_iff_finiteType S₁).mp hS₁fg
  haveI : IsNoetherianRing ↥S₁ := Algebra.FiniteType.isNoetherianRing ℤ ↥S₁

  obtain ⟨Z₁, ι₁, hι₁, e₁, hpb₁, he₁⟩ :=
    AlgebraicGeometry.ProjSpace.exists_isClosedImmersion_isPullback_comp_eq_map ι₀ ↥S₁
  rw [hι₀f] at hpb₁
  set f₁ : Z₁ ⟶ Spec (CommRingCat.of ↥S₁) := ι₁ ≫ ProjSpace.π ↥S₁ N₀ with hf₁
  haveI : IsClosedImmersion ι₁ := hι₁
  haveI : IsProper f₁ := MorphismProperty.of_isPullback hpb₁ hpr₀
  haveI : Smooth f₁ := MorphismProperty.of_isPullback hpb₁ hsm₀
  have hloc₁ := hU₀bc ↥S₁ (algebraMap ↥S₀ ↥S₁) Z₁ f₁ e₁ hpb₁
  have hab₁ : ∀ (s : ↥(Spec (CommRingCat.of ↥S₁))) (k : Type) [Field k] [IsAlgClosed k] (x : ↥S₁ →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f₁ (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f₁ (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f₁ (Spec.map (CommRingCat.ofHom x))) = g ∧
        Nonempty (RelativeGroupLaw k (pullback.snd f₁ (Spec.map (CommRingCat.ofHom x)))) := by
    intro s
    exact (Set.ext_iff.mp hloc₁ s).mpr (hS₁U s)
  obtain ⟨hsm₁, hconn₁, -, hbund₁⟩ :=
    GoodReductionJacobian.smooth_and_isConnected_preimage_and_abelianSchemePropertyBundle_of_forall_geometricFibre f₁ g hab₁

  let ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥S₁))) f₁ :=
    ⟨hpb₁.lift (Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ ↥S₁)) ≫ ε₀.1) (𝟙 _)
        (by rw [Category.assoc, ε₀.2, Category.comp_id, Category.id_comp]),
      hpb₁.lift_snd _ _ _⟩
  have hε₁ : ε₁.1 ≫ e₁ = Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ ↥S₁)) ≫ ε₀.1 := hpb₁.lift_fst _ _ _
  obtain ⟨L₁, hone₁, hcomm₁, -⟩ :=
    GoodReductionJacobian.exists_relativeGroupLaw_one_eq_and_isCommutative_of_smooth_of_isClosedImmersion_proj_of_isNoetherianRing
      f₁ hsm₁ inferInstance hconn₁ N₀ ι₁ hι₁ rfl ε₁ hbund₁

  let g₁ : Z ⟶ Z₁ := hpb₁.lift gg (f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R)))
    (by rw [hpb.w, Category.assoc, ← hbb])
  have hg₁e : g₁ ≫ e₁ = gg := hpb₁.lift_fst _ _ _
  have hg₁f : g₁ ≫ f₁ = f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R)) := hpb₁.lift_snd _ _ _
  have hbig : IsPullback (g₁ ≫ e₁) f f₀
      (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R)) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ ↥S₁))) := by
    rw [hg₁e, ← hbb]; exact hpb
  have hg₁ : IsPullback g₁ f f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R))) :=
    IsPullback.of_right hbig hg₁f hpb₁

  obtain ⟨L, -, hLone, hLcomm⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_forall_mul_comp_eq_of_isPullback f₁ f g₁ hg₁ L₁

  have hone : L.one (𝟙 _) = ε := by
    apply Subtype.ext
    apply hg₁.hom_ext
    · rw [hLone]

      have h1 := congrArg Subtype.val (L₁.one_natural (𝟙 _) (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R)))
        (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R))) (by simp))
      rw [GoodReductionJacobian.schemeHomOverComp_coe, hone₁] at h1
      rw [← h1]
      apply hpb₁.hom_ext
      · rw [Category.assoc, hε₁, Category.assoc, hg₁e, hε₀, ← Category.assoc, ← hbb]
      · rw [Category.assoc, ε₁.2, Category.assoc, hg₁f, ← Category.assoc, ε.2, Category.comp_id, Category.id_comp]
    · rw [(L.one (𝟙 _)).2, ε.2]
  refine ⟨L, hone, hLcomm hcomm₁, fun L' hL' => ?_⟩

  have hA : AbelianSchemePropertyBundle R f := ⟨hsm, inferInstance, hconnR, ⟨L⟩⟩
  exact GoodReductionJacobian.RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle hA L' L (hL'.trans hone.symm)

end S_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_and_isCommutative_of_forall_abelian_geometricFibre
end P2MW
export P2MW.S_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_and_isCommutative_of_forall_abelian_geometricFibre (solution)

-- Prove2me | solution 1 for ModularCurve.XHDRLevel.range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/817e45c2-acbb-5d3d-87fb-407c92ed3a5b

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_AlgebraicGeometry_mem_smoothLocus_of_not_mem_range_of_isClosedImmersion
import Theorems.Thm_ModularCurve_DRLevel_exists_place_residueField_ringHom_comp_eq
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    [Flat (toBase p (ΓM M H) hj)] [LocallyOfFinitePresentation (toBase p (ΓM M H) hj)]
    [SmoothOfRelativeDimension 1 (toBase p (ΓN p M H hpM) hj)]
    (U : (X p (ΓM M H) hj).Opens)
    (hUmax : ∀ V : (X p (ΓM M H) hj).Opens, Smooth (V.ι ≫ toBase p (ΓM M H) hj) → V ≤ U)
    (fibre_reduced : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
      IsReduced (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (comp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
      Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶
        fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (comp_over : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (i : Fin 2),
      comp A hA ρ hρ i ≫ pullback.snd _ _ = pullback.snd _ _)
    (comp_isClosedImmersion : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (i : Fin 2),
      IsClosedImmersion (comp A hA ρ hρ i))
    (comp_jointly_surjective : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
      (y : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      y ∈ Set.range (comp A hA ρ hρ 0).base ∨ y ∈ Set.range (comp A hA ρ hρ 1).base)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj))
    (ε_off_comp1 : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
      Set.range (sectionFibre ε ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ (Set.range (comp A hA ρ hρ 1).base)ᶜ) :
    Set.range ε.1.base ⊆ (U : Set (X p (ΓM M H) hj)) := by
  classical

  let κ₀ : Type := AlgebraicClosure (ZMod p)
  let toκ₀ : R p →+* κ₀ := (algebraMap (ZMod p) κ₀).comp (GaloisRep.ratLocalizedAtResidue p)
  obtain ⟨A, hA, hchar, halg, ρ, hρ, -, -⟩ :=
    ModularCurve.DRLevel.exists_place_residueField_ringHom_comp_eq p κ₀ toκ₀
  haveI := hchar
  haveI := halg
  set toκ : R p →+* IsLocalRing.ResidueField ↥A := (IsLocalRing.residue ↥A).comp ρ with htoκ

  haveI : IsReduced (fibre (Γ := ΓM M H) (hj := hj) toκ) := fibre_reduced A hA ρ hρ
  haveI : IsClosedImmersion (comp A hA ρ hρ 0) := comp_isClosedImmersion A hA ρ hρ 0
  haveI : IsClosedImmersion (comp A hA ρ hρ 1) := comp_isClosedImmersion A hA ρ hρ 1
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom toκ))) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

  set c₀ := IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A) with hc₀
  set y₀ := (sectionFibre ε toκ).base c₀ with hy₀def
  have hy₀ : y₀ ∉ Set.range (comp A hA ρ hρ 1).base := fun h => ε_off_comp1 A hA ρ hρ ⟨c₀, rfl⟩ h
  have hsm : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))).base y₀ ∈
      (toBase p (ΓM M H) hj).smoothLocus :=
    AlgebraicGeometry.mem_smoothLocus_of_not_mem_range_of_isClosedImmersion
      (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom toκ)))
      (comp A hA ρ hρ 0) (comp A hA ρ hρ 1) (comp_over A hA ρ hρ 0) (comp_jointly_surjective A hA ρ hρ)
      y₀ hy₀

  have hSL : (toBase p (ΓM M H) hj).smoothLocus ≤ U := by
    apply hUmax
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, Scheme.Opens.ι_preimage_self]

  set s₀ := (Spec.map (CommRingCat.ofHom toκ)).base c₀ with hs₀def
  have hfac : sectionFibre ε toκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom toκ) ≫ ε.1 := by
    delta ModularCurve.XHDRLevel.sectionFibre
    exact pullback.lift_fst _ _ _
  have hfst : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))).base y₀ = ε.1.base s₀ := by
    rw [hy₀def, hs₀def, ← TopCat.comp_app, ← Scheme.Hom.comp_base, hfac, Scheme.Hom.comp_base, TopCat.comp_app]
  have hp0 : toκ (p : R p) = 0 := by
    rw [htoκ, RingHom.comp_apply, map_natCast, IsLocalRing.residue_eq_zero_iff]
    obtain ⟨h, hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hA
    have : (⟨(p : AlgebraicClosure ℚ), h⟩ : ↥A) = (p : ↥A) := Subtype.ext (by simp)
    rwa [this] at hm
  haveI : IsDiscreteValuationRing (R p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  have hle : IsLocalRing.maximalIdeal (R p) ≤ s₀.asIdeal := by
    rw [GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out, Ideal.span_le,
      Set.singleton_subset_iff]
    show (p : R p) ∈ ((Spec.map (CommRingCat.ofHom toκ)).base c₀).asIdeal
    rw [show (Spec.map (CommRingCat.ofHom toκ)).base c₀ = PrimeSpectrum.comap toκ c₀ from rfl,
      PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hp0]
    exact Ideal.zero_mem _
  rintro _ ⟨s, rfl⟩
  have hspec : ε.1.base s ⤳ ε.1.base s₀ := by
    refine Specializes.map ?_ ε.1.base.hom.continuous
    exact (PrimeSpectrum.le_iff_specializes s s₀).mp ((IsLocalRing.le_maximalIdeal s.isPrime.ne_top).trans hle)
  exact hspec.mem_open U.isOpen (hSL (hfst ▸ hsm))

end S_ModularCurve_XHDRLevel_range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one (solution)

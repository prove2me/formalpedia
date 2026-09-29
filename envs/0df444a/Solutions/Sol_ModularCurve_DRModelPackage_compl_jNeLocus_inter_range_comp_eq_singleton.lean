-- Prove2me | solution 1 for ModularCurve.DRModelPackage.compl_jNeLocus_inter_range_comp_eq_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/949c4400-c32b-5c20-9441-62d8319cb290

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Theorems.Thm_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_compl_jNeLocus_inter_range_comp_eq_singleton
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

namespace FbPlus

section Topology

open Set Topology

variable {X : Type*} [TopologicalSpace X]

theorem irred_subset_or {S Z₁ Z₂ : Set X} (hS : IsIrreducible S) (h₁ : IsClosed Z₁) (h₂ : IsClosed Z₂)
    (h : S ⊆ Z₁ ∪ Z₂) : S ⊆ Z₁ ∨ S ⊆ Z₂ :=
  (isPreirreducible_iff_isClosed_union_isClosed.mp hS.isPreirreducible) Z₁ Z₂ h₁ h₂ h

theorem pair_eq_of_irreducible_closed_covers {A B A' B' : Set X}
    (hA : IsIrreducible A) (hB : IsIrreducible B) (hAc : IsClosed A) (hBc : IsClosed B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B)
    (hA' : IsIrreducible A') (hB' : IsIrreducible B') (hA'c : IsClosed A') (hB'c : IsClosed B')
    (hcov' : ∀ x, x ∈ A' ∨ x ∈ B')
    (hAB' : ¬ A' ⊆ B') (hBA' : ¬ B' ⊆ A') :
    (A = A' ∧ B = B') ∨ (A = B' ∧ B = A') := by
  have cov : ∀ S : Set X, S ⊆ A ∪ B := fun S x _ => hcov x
  have cov' : ∀ S : Set X, S ⊆ A' ∪ B' := fun S x _ => hcov' x
  have hA_or := irred_subset_or hA hA'c hB'c (cov' A)
  have hB_or := irred_subset_or hB hA'c hB'c (cov' B)
  have hA'_or := irred_subset_or hA' hAc hBc (cov A')
  have hB'_or := irred_subset_or hB' hAc hBc (cov B')

  rcases hA'_or with hA'A | hA'B
  ·
    have hAA' : A ⊆ A' := by
      rcases hA_or with h | h
      · exact h
      · exact absurd (hA'A.trans h) hAB'
    have eA : A = A' := hAA'.antisymm hA'A
    refine Or.inl ⟨eA, ?_⟩
    rcases hB'_or with hB'A | hB'B
    · exact absurd (hB'A.trans hAA') hBA'
    · refine (?_ : B ⊆ B').antisymm hB'B
      rcases hB_or with h | h
      ·
        exfalso; apply hBA'
        intro x hx
        rcases hcov x with hxA | hxB
        · exact hAA' hxA
        · exact h hxB
      · exact h
  ·
    have hBA'' : B ⊆ A' := by
      rcases hB_or with h | h
      · exact h
      · exact absurd (hA'B.trans h) hAB'
    have eB : B = A' := hBA''.antisymm hA'B
    refine Or.inr ⟨?_, eB⟩
    rcases hB'_or with hB'A | hB'B
    · refine (?_ : A ⊆ B').antisymm hB'A
      rcases hA_or with h | h
      · exfalso; apply hBA'
        intro x hx
        rcases hcov x with hxA | hxB
        · exact h hxA
        · exact hBA'' hxB
      · exact h
    · exact absurd (hB'B.trans hBA'') hBA'

theorem mem_cover_eq_or {A B A' B' S : Set X}
    (hA : IsIrreducible A) (hB : IsIrreducible B) (hAc : IsClosed A) (hBc : IsClosed B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B)
    (hA' : IsIrreducible A') (hB' : IsIrreducible B') (hA'c : IsClosed A') (hB'c : IsClosed B')
    (hcov' : ∀ x, x ∈ A' ∨ x ∈ B')
    (hAB' : ¬ A' ⊆ B') (hBA' : ¬ B' ⊆ A') (hS : S = A ∨ S = B) :
    S = A' ∨ S = B' := by
  rcases pair_eq_of_irreducible_closed_covers hA hB hAc hBc hcov hA' hB' hA'c hB'c hcov' hAB' hBA' with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hS
  · exact hS.symm

end Topology

section SchemeTransport

open Set Topology

universe u

variable {X : Scheme.{u}}

theorem isClosed_range_of_isClosedImmersion {Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f] :
    IsClosed (Set.range f.base) :=
  f.isClosedEmbedding.isClosed_range

theorem isIrreducible_range_of_irreducibleSpace {Y : Scheme.{u}} [IrreducibleSpace Y] (f : Y ⟶ X) :
    IsIrreducible (Set.range f.base) := by
  rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ Y).image f.base f.continuous.continuousOn

theorem transport_singleton {Y Y' : Scheme.{u}} (f : Y ⟶ X) (g : Y' ⟶ X) [IsClosedImmersion f]
    [IsClosedImmersion g] (hfg : Set.range f.base = Set.range g.base) (L : Set X)
    (h : ∃ y : closedPoints Y', L ∩ Set.range g.base = {g.base y.1}) :
    ∃ x : closedPoints Y, L ∩ Set.range f.base = {f.base x.1} := by
  obtain ⟨⟨y, hy⟩, hL⟩ := h
  have hmem : g.base y ∈ Set.range f.base := by
    rw [hfg]; exact ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  have hclosed_pt : IsClosed ({g.base y} : Set X) := by
    rw [← Set.image_singleton]
    exact g.isClosedEmbedding.isClosedMap _ ((mem_closedPoints_iff).mp hy)
  have hxclosed : IsClosed ({x} : Set Y) := by
    have : ({x} : Set Y) = f.base ⁻¹' {g.base y} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact hx
      · intro hz; exact f.isClosedEmbedding.injective (hz.trans hx.symm)
    rw [this]
    exact hclosed_pt.preimage f.continuous
  refine ⟨⟨x, (mem_closedPoints_iff).mpr hxclosed⟩, ?_⟩
  rw [hfg, hL, hx]

end SchemeTransport

section Main

p2m_open "Set Topology AlgebraicCurve.TwoChartIntegralModel"

variable (p : ℕ) [Fact p.Prime] [NeZero p] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]

structure TwoLines where
  Y₁ : Scheme.{0}
  Y₂ : Scheme.{0}
  [irr₁ : IrreducibleSpace Y₁]
  [irr₂ : IrreducibleSpace Y₂]
  c₁ : Y₁ ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))
  c₂ : Y₂ ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))
  [ci₁ : IsClosedImmersion c₁]
  [ci₂ : IsClosedImmersion c₂]
  cover : ∀ x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
    x ∈ Set.range c₁.base ∨ x ∈ Set.range c₂.base
  not_subset₁₂ : ¬ Set.range c₁.base ⊆ Set.range c₂.base
  not_subset₂₁ : ¬ Set.range c₂.base ⊆ Set.range c₁.base
  level₁ : ∀ c : κ, ∃ x : closedPoints Y₁,
      ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range c₁.base =
        {c₁.base x.1}
  level₂ : ∀ c : κ, ∃ x : closedPoints Y₂,
      ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range c₂.base =
        {c₂.base x.1}
  cusp₁ : ∃ x : closedPoints Y₁,
      ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range c₁.base =
        {c₁.base x.1}
  cusp₂ : ∃ x : closedPoints Y₂,
      ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range c₂.base =
        {c₂.base x.1}

attribute [scoped instance] TwoLines.irr₁ TwoLines.irr₂ TwoLines.ci₁ TwoLines.ci₂

variable {p κ}

theorem main_aux (𝔛 : DRModelPackage p) (T : TwoLines p κ) {Y : Scheme.{0}} [IrreducibleSpace Y]
    (C : Y ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) [IsClosedImmersion C]
    (hS : Set.range C.base = Set.range (𝔛.compInf κ).base ∨ Set.range C.base = Set.range (𝔛.compZero κ).base) :
    (∀ c : κ, ∃ x : closedPoints Y,
      ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range C.base =
        {C.base x.1}) ∧
    (∃ x : closedPoints Y,
      ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range C.base =
        {C.base x.1}) := by
  haveI := 𝔛.compInf_isClosedImmersion κ
  haveI := 𝔛.compZero_isClosedImmersion κ

  have hC : Set.range C.base = Set.range T.c₁.base ∨ Set.range C.base = Set.range T.c₂.base :=
    mem_cover_eq_or
      (isIrreducible_range_of_irreducibleSpace (𝔛.compInf κ))
      (isIrreducible_range_of_irreducibleSpace (𝔛.compZero κ))
      (isClosed_range_of_isClosedImmersion (𝔛.compInf κ))
      (isClosed_range_of_isClosedImmersion (𝔛.compZero κ))
      (𝔛.comp_jointly_surjective κ)
      (isIrreducible_range_of_irreducibleSpace T.c₁)
      (isIrreducible_range_of_irreducibleSpace T.c₂)
      (isClosed_range_of_isClosedImmersion T.c₁)
      (isClosed_range_of_isClosedImmersion T.c₂)
      T.cover T.not_subset₁₂ T.not_subset₂₁ hS
  rcases hC with h | h
  · exact ⟨fun c => transport_singleton C T.c₁ h _ (T.level₁ c), transport_singleton C T.c₁ h _ T.cusp₁⟩
  · exact ⟨fun c => transport_singleton C T.c₂ h _ (T.level₂ c), transport_singleton C T.c₂ h _ T.cusp₂⟩

theorem solution_of_twoLines (𝔛 : DRModelPackage p) (T : TwoLines p κ)
    (C : (𝔛.ratModel κ).C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))
    (hC : C = 𝔛.compInf κ ∨ C = 𝔛.compZero κ) :
    (∀ c : κ, ∃ x : closedPoints (𝔛.ratModel κ).C,
      ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range C.base =
        {C.base x.1}) ∧
    (∃ x : closedPoints (𝔛.ratModel κ).C,
      ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range C.base =
        {C.base x.1}) := by
  rcases hC with rfl | rfl
  · haveI := 𝔛.compInf_isClosedImmersion κ
    exact main_aux 𝔛 T (𝔛.compInf κ) (Or.inl rfl)
  · haveI := 𝔛.compZero_isClosedImmersion κ
    exact main_aux 𝔛 T (𝔛.compZero κ) (Or.inr rfl)

end Main

section Witness

variable (p : ℕ) [Fact p.Prime] [NeZero p] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]

theorem nonempty_twoLines : Nonempty (TwoLines p κ) := by
  classical
  obtain ⟨M, cInf, cZero, -, -, hciInf, hciZero, hcov, ⟨a, ha₁, ha₂⟩, ⟨b, hb₁, hb₂⟩, hlevInf, hlevZero,
      hcuspInf, hcuspZero⟩ :=
    ModularCurve.DRModel.exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton p κ
  exact ⟨{ Y₁ := M.C, Y₂ := M.C, c₁ := cInf, c₂ := cZero, ci₁ := hciInf, ci₂ := hciZero, cover := hcov,
           not_subset₁₂ := fun h => ha₂ (h ha₁), not_subset₂₁ := fun h => hb₂ (h hb₁),
           level₁ := hlevInf, level₂ := hlevZero, cusp₁ := hcuspInf, cusp₂ := hcuspZero }⟩

end Witness

end FbPlus
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_compl_jNeLocus_inter_range_comp_eq_singleton.FbPlus"

open FbPlus in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (C : (𝔛.ratModel κ).C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))
    (hC : C = 𝔛.compInf κ ∨ C = 𝔛.compZero κ) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    (∀ c : κ, ∃ x : closedPoints (𝔛.ratModel κ).C,
      ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range C.base =
        {C.base x.1}) ∧
    (∃ x : closedPoints (𝔛.ratModel κ).C,
      ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range C.base =
        {C.base x.1}) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact solution_of_twoLines 𝔛 (Classical.choice (nonempty_twoLines p κ)) C hC

end S_ModularCurve_DRModelPackage_compl_jNeLocus_inter_range_comp_eq_singleton
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_compl_jNeLocus_inter_range_comp_eq_singleton (solution)

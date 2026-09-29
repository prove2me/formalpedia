-- Prove2me | solution 1 for ModularCurve.res_mem_regularDifferentialsBar_of_chartMap_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/df206e51-4fd6-5c59-9252-8b1bac1bea82

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_kaehlerToFunctionField_mem_regularDifferentials
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv
import Theorems.Thm_ModularCurve_exists_ringEquiv_functionField_pullback_comp_baseToFunctionField_eq_and_germToFunctionField_eq_chartMap_of_neZero
import Theorems.Thm_ModularCurve_isIntegral_pullback_and_nonempty_of_chartMap_of_neZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_res_mem_regularDifferentialsBar_of_chartMap_of_neZero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar N))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))
    (hιinj : Function.Injective ι)
    (hιrat : ∀ a : (𝒱.cover c).A0, ∃ x ∈ modularFunctionFieldFull N,
      coeffEmb (AlgebraicClosure ℚ) x = (ι a : LaurentSeries (AlgebraicClosure ℚ)))
    (hιfrac : ∀ x ∈ modularFunctionFieldFull N, ∃ a b : (𝒱.cover c).A0, ι b ≠ 0 ∧
      coeffEmb (AlgebraicClosure ℚ) x * (ι b : LaurentSeries (AlgebraicClosure ℚ)) = ι a)
    (res : ↥((𝒱.kaehlerSections c).H0) →+ Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])
    (hres : ∀ ω : ↥((𝒱.kaehlerSections c).H0),
      res ω = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR ω.val.1)
    (ω : ↥((𝒱.kaehlerSections c).H0)) :
    res ω ∈ regularDifferentialsBar N := by
  classical
  obtain ⟨hint, hne0, hne1⟩ := ModularCurve.isIntegral_pullback_and_nonempty_of_chartMap_of_neZero N p c 𝒱 ι hιR hιinj hιrat hιfrac
  haveI := hint; haveI := hne0; haveI := hne1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) := by
    haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
      smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c _ inferInstance

  let ω' := Scheme.TwoAffineOpenCover.kaehlerH0baseChangeMap 𝒱 c (AlgebraicClosure ℚ) ω
  have h95 := AlgebraicGeometry.Scheme.TwoAffineOpenCover.kaehlerToFunctionField_mem_regularDifferentials
    (𝒱.pullback c (AlgebraicClosure ℚ)) (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) ω'

  obtain ⟨Φ, hΦc, hΦι⟩ := ModularCurve.exists_ringEquiv_functionField_pullback_comp_baseToFunctionField_eq_and_germToFunctionField_eq_chartMap_of_neZero N p c 𝒱 ι hιR hιinj hιrat hιfrac
  letI : Algebra (AlgebraicClosure ℚ) (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).functionField := (baseToFunctionField (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).toAlgebra
  let Φa : (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).functionField ≃ₐ[(AlgebraicClosure ℚ)] ↥(modularFunctionFieldBar N) :=
    AlgEquiv.ofRingEquiv (f := Φ) (fun x => by
      show Φ.toRingHom ((baseToFunctionField (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) x) = _
      rw [← RingHom.comp_apply, hΦc])

  haveI hICB : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N
  haveI hICX : IsCurveOver (AlgebraicClosure ℚ) (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).functionField :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) (RingEquiv.refl _) (fun a => rfl)
  haveI hEB : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := ModularCurve.essFiniteType_modularFunctionFieldBar N
  haveI hEX : Algebra.EssFiniteType (AlgebraicClosure ℚ) (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).functionField :=
    (Algebra.EssFiniteType.iff_of_algEquiv Φa).mpr hEB
  haveI hDCX : ∀ v : Place (AlgebraicClosure ℚ) (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).functionField, v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  haveI hDCB : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hreg := AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv Φa _ h95

  have key : Differential.pullbackAlong (Φa : (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).functionField →ₐ[(AlgebraicClosure ℚ)] ↥(modularFunctionFieldBar N))
      (kaehlerToFunctionField (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) (𝒱.pullback c (AlgebraicClosure ℚ)).U0 ω'.val.1) = res ω := by
    have hω'1 : ω'.val.1 = (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c (AlgebraicClosure ℚ)).kaehlerMap0 ω.val.1 := rfl
    rw [hω'1, hres]
    have hh := KaehlerDifferential.addMonoidHom_ext_smul_D
      (f := (((Differential.pullbackAlong (Φa : (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).functionField →ₐ[(AlgebraicClosure ℚ)] ↥(modularFunctionFieldBar N))).toAddMonoidHom.comp
              (kaehlerToFunctionField (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) (𝒱.pullback c (AlgebraicClosure ℚ)).U0).toAddMonoidHom).comp
              (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c (AlgebraicClosure ℚ)).kaehlerMap0.toAddMonoidHom))
      (g := (KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR).toAddMonoidHom)
      (fun a a' => by
        have e1 : (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c (AlgebraicClosure ℚ)).kaehlerMap0 (a • KaehlerDifferential.D ↥(GaloisRep.ratLocalizedAt p) ((𝒱.cover c).A0) a') =
            (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c (AlgebraicClosure ℚ)).ringHom0 a • KaehlerDifferential.D (AlgebraicClosure ℚ) (((𝒱.pullback c (AlgebraicClosure ℚ)).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).A0) ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c (AlgebraicClosure ℚ)).ringHom0 a') :=
          KaehlerDifferential.mapOfRingHom_smul_D _ _ _ a a'
        have e2 := KaehlerDifferential.mapOfRingHom_smul_D (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR a a'
        change (Differential.pullbackAlong (Φa : (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).functionField →ₐ[(AlgebraicClosure ℚ)] ↥(modularFunctionFieldBar N)))
            ((kaehlerToFunctionField (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) (𝒱.pullback c (AlgebraicClosure ℚ)).U0)
              ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c (AlgebraicClosure ℚ)).kaehlerMap0 (a • KaehlerDifferential.D ↥(GaloisRep.ratLocalizedAt p) ((𝒱.cover c).A0) a'))) =
          (KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR) (a • KaehlerDifferential.D ↥(GaloisRep.ratLocalizedAt p) ((𝒱.cover c).A0) a')
        rw [e2, e1]
        have e3 : ∀ (x : (((𝒱.pullback c (AlgebraicClosure ℚ)).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).A0)) (η : Ω[(((𝒱.pullback c (AlgebraicClosure ℚ)).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).A0)⁄(AlgebraicClosure ℚ)]),
            kaehlerToFunctionField (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) (𝒱.pullback c (AlgebraicClosure ℚ)).U0 (x • η) =
              ((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).germToFunctionField (𝒱.pullback c (AlgebraicClosure ℚ)).U0).hom x • kaehlerToFunctionField (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) (𝒱.pullback c (AlgebraicClosure ℚ)).U0 η :=
          fun x η => kaehlerToFunctionField_smul (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) (𝒱.pullback c (AlgebraicClosure ℚ)).U0 x η
        have e4 : ∀ (y : (((𝒱.pullback c (AlgebraicClosure ℚ)).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).A0)),
            kaehlerToFunctionField (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) (𝒱.pullback c (AlgebraicClosure ℚ)).U0 (KaehlerDifferential.D (AlgebraicClosure ℚ) (((𝒱.pullback c (AlgebraicClosure ℚ)).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).A0) y) =
              KaehlerDifferential.D (AlgebraicClosure ℚ) (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).functionField (((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).germToFunctionField (𝒱.pullback c (AlgebraicClosure ℚ)).U0).hom y) :=
          fun y => kaehlerToFunctionField_D (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) (𝒱.pullback c (AlgebraicClosure ℚ)).U0 y
        rw [e3, e4, Differential.pullbackAlong_smul, Differential.pullbackAlong_D]
        have e5 : ∀ z, (Φa : (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).functionField →ₐ[(AlgebraicClosure ℚ)] ↥(modularFunctionFieldBar N)) z = Φ z := fun z => rfl
        rw [e5, e5, hΦι a, hΦι a'])
    exact DFunLike.congr_fun hh ω.val.1
  rw [← key]
  exact hreg

end S_ModularCurve_res_mem_regularDifferentialsBar_of_chartMap_of_neZero
end P2MW
export P2MW.S_ModularCurve_res_mem_regularDifferentialsBar_of_chartMap_of_neZero (solution)

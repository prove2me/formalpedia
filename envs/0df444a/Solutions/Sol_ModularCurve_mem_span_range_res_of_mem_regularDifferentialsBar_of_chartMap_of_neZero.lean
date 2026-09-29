-- Prove2me | solution 1 for ModularCurve.mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e4f78207-d7b0-57e0-bf78-30fbfa63e5bc

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_kaehlerSections
import Theorems.Thm_ModularCurve_isIntegral_pullback_and_nonempty_of_chartMap_of_neZero
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField
import Theorems.Thm_ModularCurve_exists_ringEquiv_functionField_pullback_comp_baseToFunctionField_eq_and_germToFunctionField_eq_chartMap_of_neZero
import Theorems.Thm_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve

p2m_open "CategoryTheory.Limits AlgebraicCurve P2MW.S_ModularCurve_mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero.AlgebraicCurve"
open scoped TensorProduct

namespace SpanN

theorem spanN_bcSide
    {R : Type} [CommRing R] {X : Scheme.{0}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (CommRingCat.of R))
    (A : Type) [CommRing A] [Algebra R A] [Module.Flat R A]
    (θ : ↥(((𝒱.pullback c A).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H0)) :
    θ ∈ Submodule.span A (Set.range (Scheme.TwoAffineOpenCover.kaehlerH0baseChangeMap 𝒱 c A)) := by
  classical
  obtain ⟨e0, e1, e01, eH0, eH1, he0, he1, -, heH0, -⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_kaehlerSections 𝒱 c A

  have hexact : Function.Exact (𝒱.kaehlerSections c).H0.subtype (𝒱.kaehlerSections c).cechDiff :=
    LinearMap.exact_subtype_ker_map _
  have hexactA : Function.Exact ((𝒱.kaehlerSections c).H0.subtype.lTensor A) ((𝒱.kaehlerSections c).cechDiff.lTensor A) := Module.Flat.lTensor_exact A hexact

  have hmem : ∀ t : A ⊗[R] ↥((𝒱.kaehlerSections c).H0), ((𝒱.kaehlerSections c).H0.subtype.baseChange A) t ∈ LinearMap.ker ((𝒱.kaehlerSections c).cechDiff.baseChange A) := by
    intro t
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.comp_ker_subtype,
      LinearMap.baseChange_zero, LinearMap.zero_apply]
  let L : A ⊗[R] ↥((𝒱.kaehlerSections c).H0) →ₗ[A] ↥(((𝒱.pullback c A).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H0) :=
    eH0.toLinearMap ∘ₗ LinearMap.codRestrict _ ((𝒱.kaehlerSections c).H0.subtype.baseChange A) hmem

  have hL1 : ∀ ω : ↥((𝒱.kaehlerSections c).H0), L (1 ⊗ₜ[R] ω) = Scheme.TwoAffineOpenCover.kaehlerH0baseChangeMap 𝒱 c A ω := by
    intro ω
    apply Subtype.ext
    simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [heH0, Scheme.TwoAffineOpenCover.HomOver.kaehlerH0map_apply_coe]
    simp only [LinearMap.codRestrict_apply, LinearMap.baseChange_tmul, Submodule.coe_subtype]
    have hp : ((ω : ↥((𝒱.kaehlerSections c).H0)) : (𝒱.kaehlerSections c).M0 × (𝒱.kaehlerSections c).M1) =
        (((ω : ↥((𝒱.kaehlerSections c).H0)) : (𝒱.kaehlerSections c).M0 × (𝒱.kaehlerSections c).M1).1,
         ((ω : ↥((𝒱.kaehlerSections c).H0)) : (𝒱.kaehlerSections c).M0 × (𝒱.kaehlerSections c).M1).2) := rfl
    rw [hp, TensorProduct.prodRight_tmul]
    simp only [he0, he1, one_smul]

  have hrange : ∀ t : A ⊗[R] ↥((𝒱.kaehlerSections c).H0), L t ∈ Submodule.span A (Set.range (Scheme.TwoAffineOpenCover.kaehlerH0baseChangeMap 𝒱 c A)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a ω =>
        have : a ⊗ₜ[R] ω = a • ((1 : A) ⊗ₜ[R] ω) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, hL1]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ω, rfl⟩)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

  obtain ⟨t, ht⟩ : ∃ t : A ⊗[R] ↥((𝒱.kaehlerSections c).H0), ((𝒱.kaehlerSections c).H0.subtype.lTensor A) t = (eH0.symm θ : A ⊗[R] _) := by
    apply (hexactA _).mp
    have h2 := (eH0.symm θ).2
    rw [LinearMap.mem_ker] at h2
    exact h2
  have hθ : θ = L t := by
    have : eH0.symm θ = ⟨((𝒱.kaehlerSections c).H0.subtype.baseChange A) t, hmem t⟩ := Subtype.ext (by rw [← ht]; rfl)
    calc θ = eH0 (eH0.symm θ) := (eH0.apply_symm_apply θ).symm
      _ = L t := by rw [this]; rfl
  rw [hθ]
  exact hrange t

end SpanN

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place Differential.pullbackAlong Differential.pullbackAlong_D Differential.pullbackAlong_smul regularDifferentials kaehlerToFunctionField kaehlerToFunctionField_D kaehlerToFunctionField_smul baseToFunctionField IsCurveOver pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one dCoordGenerates_of_isCurveOver" namespace Differential p2m_export "AlgebraicCurve.Differential" "pullbackAlong pullbackAlong_D pullbackAlong_smul" end AlgebraicCurve.Differential
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Differential" in

theorem AlgebraicCurve.Differential.pullbackAlong_apply_pullbackAlong_symm
    {K : Type*} [Field K] {F F' : Type*} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (Φ : F ≃ₐ[K] F') (η : Ω[F'⁄K]) :
    Differential.pullbackAlong (Φ : F →ₐ[K] F') (Differential.pullbackAlong (Φ.symm : F' →ₐ[K] F) η) = η := by
  have hh := KaehlerDifferential.addMonoidHom_ext_smul_D
    (f := (Differential.pullbackAlong (Φ : F →ₐ[K] F')).toAddMonoidHom.comp
      (Differential.pullbackAlong (Φ.symm : F' →ₐ[K] F)).toAddMonoidHom)
    (g := AddMonoidHom.id Ω[F'⁄K]) (fun a b => by
      change Differential.pullbackAlong (Φ : F →ₐ[K] F')
          (Differential.pullbackAlong (Φ.symm : F' →ₐ[K] F) (a • KaehlerDifferential.D K F' b)) = a • KaehlerDifferential.D K F' b
      rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_D, Differential.pullbackAlong_smul,
        Differential.pullbackAlong_D, AlgEquiv.coe_algHom, AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply,
        AlgEquiv.apply_symm_apply])
  exact DFunLike.congr_fun hh η

set_option maxHeartbeats 6400000 in
theorem spanN_omegaSide
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
    [IsIntegral (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))] [Nonempty (𝒱.pullback c (AlgebraicClosure ℚ)).U0] [Nonempty (𝒱.pullback c (AlgebraicClosure ℚ)).U1] :
    ∃ T : ↥((((𝒱.pullback c (AlgebraicClosure ℚ))).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).H0) →ₗ[AlgebraicClosure ℚ] Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ],
      (∀ ω : ↥((𝒱.kaehlerSections c).H0), T (Scheme.TwoAffineOpenCover.kaehlerH0baseChangeMap 𝒱 c (AlgebraicClosure ℚ) ω) = res ω) ∧
      (∀ η : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ], η ∈ regularDifferentialsBar N →
        ∃ θ : ↥((((𝒱.pullback c (AlgebraicClosure ℚ))).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).H0), T θ = η) := by
  classical
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) := by
    haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
      smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c _ inferInstance
  haveI : IsProper (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) := inferInstance

  obtain ⟨Φ, hΦc, hΦι⟩ :=
    ModularCurve.exists_ringEquiv_functionField_pullback_comp_baseToFunctionField_eq_and_germToFunctionField_eq_chartMap_of_neZero
      N p c 𝒱 ι hιR hιinj hιrat hιfrac
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

  obtain ⟨eΩ, heΩ⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField
      (𝒱.pullback c (AlgebraicClosure ℚ)) (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))

  refine ⟨(Differential.pullbackAlong (Φa : ((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).functionField →ₐ[(AlgebraicClosure ℚ)] ↥(modularFunctionFieldBar N))) ∘ₗ
      ((regularDifferentials (AlgebraicClosure ℚ) ((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).functionField).subtype ∘ₗ (eΩ : ↥((((𝒱.pullback c (AlgebraicClosure ℚ))).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).H0) →ₗ[(AlgebraicClosure ℚ)] ↥(regularDifferentials (AlgebraicClosure ℚ) ((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).functionField))), ?_, ?_⟩
  ·
    intro ω
    set ω' := Scheme.TwoAffineOpenCover.kaehlerH0baseChangeMap 𝒱 c (AlgebraicClosure ℚ) ω with hω'def
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
    show Differential.pullbackAlong (Φa : ((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).functionField →ₐ[(AlgebraicClosure ℚ)] ↥(modularFunctionFieldBar N)) ((eΩ ω' : ↥(regularDifferentials (AlgebraicClosure ℚ) ((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).functionField)) : Ω[((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).functionField⁄(AlgebraicClosure ℚ)]) = res ω
    rw [heΩ ω']
    exact key
  ·
    intro η hη
    have hη' : Differential.pullbackAlong (Φa.symm : ↥(modularFunctionFieldBar N) →ₐ[(AlgebraicClosure ℚ)] ((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).functionField) η ∈ regularDifferentials (AlgebraicClosure ℚ) ((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).functionField :=
      AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv Φa.symm η hη
    refine ⟨eΩ.symm ⟨_, hη'⟩, ?_⟩
    show Differential.pullbackAlong (Φa : ((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).functionField →ₐ[(AlgebraicClosure ℚ)] ↥(modularFunctionFieldBar N))
        ((eΩ (eΩ.symm ⟨_, hη'⟩) : ↥(regularDifferentials (AlgebraicClosure ℚ) ((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).functionField)) : Ω[((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))).functionField⁄(AlgebraicClosure ℚ)]) = η
    rw [LinearEquiv.apply_symm_apply]
    exact AlgebraicCurve.Differential.pullbackAlong_apply_pullbackAlong_symm Φa η

namespace SpanN

theorem flat_algebraicClosure (p : ℕ) [Fact p.Prime] : Module.Flat ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  haveI : IsScalarTower ℤ ↥(GaloisRep.ratLocalizedAt p) ℚ := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ := IsFractionRing.isFractionRing_of_isLocalization (Ideal.span {(p : ℤ)}).primeCompl ↥(GaloisRep.ratLocalizedAt p) ℚ
    (Ideal.primeCompl_le_nonZeroDivisors _)
  haveI : Module.Flat ↥(GaloisRep.ratLocalizedAt p) ℚ := IsLocalization.flat ℚ (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt p))
  exact Module.Flat.trans ↥(GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ)

end SpanN

open SpanN in
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
    (η : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) (hη : η ∈ regularDifferentialsBar N) :
    η ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range res) := by
  classical

  obtain ⟨hint, hne0, hne1⟩ :=
    ModularCurve.isIntegral_pullback_and_nonempty_of_chartMap_of_neZero N p c 𝒱 ι hιR hιinj hιrat hιfrac
  haveI := hint; haveI := hne0; haveI := hne1
  haveI : Module.Flat ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) := flat_algebraicClosure p

  obtain ⟨T, hTbc, hTsurj⟩ := spanN_omegaSide N p c 𝒱 ι hιR hιinj hιrat hιfrac res hres
  obtain ⟨θ, hθ⟩ := hTsurj η hη
  have hspan := spanN_bcSide 𝒱 c (AlgebraicClosure ℚ) θ

  rw [← hθ]
  have himg : Submodule.map T (Submodule.span (AlgebraicClosure ℚ) (Set.range (Scheme.TwoAffineOpenCover.kaehlerH0baseChangeMap 𝒱 c (AlgebraicClosure ℚ)))) ≤
      Submodule.span (AlgebraicClosure ℚ) (Set.range res) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨ω, rfl⟩, rfl⟩
    rw [hTbc]
    exact Submodule.subset_span ⟨ω, rfl⟩
  exact himg (Submodule.mem_map_of_mem hspan)

end S_ModularCurve_mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero
end P2MW
export P2MW.S_ModularCurve_mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero (solution)

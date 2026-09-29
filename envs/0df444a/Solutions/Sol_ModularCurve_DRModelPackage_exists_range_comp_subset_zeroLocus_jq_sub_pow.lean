-- Prove2me | solution 1 for ModularCurve.DRModelPackage.exists_range_comp_subset_zeroLocus_jq_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8f8c9efc-cdbd-5e0d-bf65-429f4800a87e

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgFin_valuationSubring_pair_levelP
import Theorems.Thm_ModularCurve_DRModel_exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_exists_range_comp_subset_zeroLocus_jq_sub_pow
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_range_comp_subset_zeroLocus_jq_sub_pow.ModularCurve AlgebraicCurve"
open IsLocalRing

universe u

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage qExpand jq modularFunctionFieldFull IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme DRModel.exists_chartAlgFin_valuationSubring_pair_levelP DRModel.exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "e₀ comp_jointly_surjective compZero ratModel compInf mk"
namespace HorPkg
p2m_open "ModularCurve.DRModelPackage ModularCurve"

theorem germ_app_mem_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (x : X) (hx : f.base x ∈ V) (s : Γ(Y, V)) :
    (X.presheaf.germ (f ⁻¹ᵁ V) x hx).hom ((f.app V).hom s) ∈ maximalIdeal (X.presheaf.stalk x) ↔
      (Y.presheaf.germ V (f.base x) hx).hom s ∈ maximalIdeal (Y.presheaf.stalk (f.base x)) := by
  rw [← Scheme.Hom.germ_stalkMap_apply f V x hx s, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

theorem germ_ΓSpecIso_inv_mem_iff (R : CommRingCat.{u}) (q : PrimeSpectrum R) (t : R) :
    ((Spec R).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso R).inv t) ∈ maximalIdeal ((Spec R).presheaf.stalk q) ↔
      t ∈ q.asIdeal := by
  have h1 : ((Spec R).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso R).inv t) =
      (StructureSheaf.toStalk R q).hom t := rfl
  have h2 : IsUnit ((StructureSheaf.toStalk R q).hom t) ↔ t ∈ q.asIdeal.primeCompl := by
    rw [← StructureSheaf.stalkAlgebra_map]
    exact IsLocalization.AtPrime.isUnit_to_map_iff _ q.asIdeal t
  have h3 : t ∈ q.asIdeal.primeCompl ↔ t ∉ q.asIdeal := Iff.rfl
  rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact (not_congr h2).trans ((not_congr h3).trans not_not)

theorem germ_appIso_inv_mem_iff {Y : Scheme.{u}} (R : CommRingCat.{u}) (ι : Spec R ⟶ Y) [IsOpenImmersion ι]
    (q : PrimeSpectrum R) (hq : ι.base q ∈ ι ''ᵁ ⊤) (t : R) :
    (Y.presheaf.germ (ι ''ᵁ ⊤) (ι.base q) hq).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv t)) ∈
        maximalIdeal (Y.presheaf.stalk (ι.base q)) ↔ t ∈ q.asIdeal := by
  rw [← germ_app_mem_iff ι (ι ''ᵁ ⊤) q hq]
  have hmor : (ι.appIso ⊤).inv ≫ ι.app (ι ''ᵁ ⊤) ≫ (Spec R).presheaf.germ (ι ⁻¹ᵁ ι ''ᵁ ⊤) q hq =
      (Spec R).presheaf.germ ⊤ q trivial := by
    rw [Scheme.Hom.appIso_inv_app_assoc]
    exact TopCat.Presheaf.germ_res _ _ _ _
  have : ((Spec R).presheaf.germ (ι ⁻¹ᵁ ι ''ᵁ ⊤) q hq).hom
        ((ι.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv t))) =
      ((Spec R).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso R).inv t) :=
    congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso R).inv t)) hmor
  rw [this, germ_ΓSpecIso_inv_mem_iff]

theorem isPreirreducible_range {C X : Scheme.{u}} [IrreducibleSpace C] (g : C ⟶ X) :
    IsPreirreducible (Set.range g.base) := by
  rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ C).isPreirreducible.image _ g.continuous.continuousOn

theorem comap_eq_span_of_natCast_mem {B : Type*} [CommRing B] (p : ℕ) (hp : p.Prime) (f : ℤ →+* B) (Q : Ideal B)
    [Q.IsPrime] (h : (p : B) ∈ Q) : Q.comap f = Ideal.span {(p : ℤ)} := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := by
    have h' : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpz.ne_zero).mpr hpz
    exact h'.isMaximal (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact hpz.ne_zero)
  refine (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact h

theorem exists_const_of_frobenius_pair {A B κ : Type*} [CommRing A] [CommRing B] [IsLocalRing B] [Field κ]
    [IsAlgClosed κ] (p : ℕ) (hp : p.Prime) (φ : A →+* B) (ψ : κ →+* B) (j jp : A)
    (h1 : φ (j - jp ^ p) ∈ maximalIdeal B) (h2 : φ (jp - j ^ p) ∈ maximalIdeal B) :
    ∃ c : κ, c ^ (p ^ 2) = c ∧ φ j - ψ c ∈ maximalIdeal B := by
  have hu : residue B (φ j) = residue B (φ jp) ^ p := by
    rw [← sub_eq_zero, ← map_pow, ← map_pow, ← map_sub, ← map_sub]
    exact (residue_eq_zero_iff _).mpr h1
  have hv : residue B (φ jp) = residue B (φ j) ^ p := by
    rw [← sub_eq_zero, ← map_pow, ← map_pow, ← map_sub, ← map_sub]
    exact (residue_eq_zero_iff _).mpr h2
  have hfix : residue B (φ j) ^ (p ^ 2) = residue B (φ j) := by
    rw [sq, pow_mul, ← hv, ← hu]
  letI : Algebra κ (ResidueField B) := ((residue B).comp ψ).toAlgebra
  have two_le : 2 ≤ p ^ 2 := by nlinarith [hp.two_le]
  have hmonic : (Polynomial.X ^ (p ^ 2) - Polynomial.X : Polynomial κ).Monic := by
    apply (Polynomial.monic_X_pow _).sub_of_left
    rw [Polynomial.degree_X_pow, Polynomial.degree_X]
    exact_mod_cast (lt_of_lt_of_le one_lt_two two_le)
  have hint : IsIntegral κ (residue B (φ j)) := by
    refine ⟨Polynomial.X ^ (p ^ 2) - Polynomial.X, hmonic, ?_⟩
    simp [hfix]
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible κ (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one κ (residue B (φ j)) hdeg
  have hc' : residue B (ψ c) = residue B (φ j) := hc
  refine ⟨c, ?_, ?_⟩
  · apply ((residue B).comp ψ).injective
    rw [map_pow, RingHom.comp_apply, hc', hfix]
  · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero, hc']

end ModularCurve.DRModelPackage.HorPkg

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage qExpand jq modularFunctionFieldFull IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme DRModel.exists_chartAlgFin_valuationSubring_pair_levelP DRModel.exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "e₀ comp_jointly_surjective compZero ratModel compInf mk"
namespace HorPkg
p2m_open "ModularCurve.DRModelPackage ModularCurve"

section Concrete

variable (p : ℕ) [Fact p.Prime] [NeZero p]

set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldFull p)
set_option quotPrecheck false in
local notation "jF" => IgusaScheme.jFull p
set_option quotPrecheck false in
local notation "AA" => ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
set_option quotPrecheck false in
local notation "ιF" => TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)

variable (κ : Type) [Field κ] [CharP κ p]

set_option quotPrecheck false in
local notation "gκ" => Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))
set_option quotPrecheck false in
local notation "Xκ" => pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))
set_option quotPrecheck false in
local notation "πκ" => pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))

theorem natCast_mem_of_base_eq (x : ↥(Xκ)) (q : PrimeSpectrum AA) (hq : (ιF).base q = (πκ).base x) :
    ((p : ℕ) : AA) ∈ q.asIdeal := by
  have h1 : (DRModel.toBase p).base ((ιF).base q) =
      (gκ).base ((pullback.snd (DRModel.toBase p) gκ).base x) := by
    rw [hq, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have h2 : (DRModel.toBase p).base ((ιF).base q) =
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ AA))).base q := by
    rw [← Scheme.Hom.comp_apply, TwoChartIntegralModel.ιFin_toBase]
  have h4 : (p : ℤ) ∈ ((gκ).base ((pullback.snd (DRModel.toBase p) gκ).base x)).asIdeal := by
    change (p : ℤ) ∈ Ideal.comap _ _
    rw [Ideal.mem_comap]
    simp
  rw [← h1, h2] at h4
  change (p : ℤ) ∈ Ideal.comap _ _ at h4
  rw [Ideal.mem_comap] at h4
  simpa using h4

theorem exists_base_eq (q : PrimeSpectrum AA) (hq : ((p : ℕ) : AA) ∈ q.asIdeal) :
    ∃ x : ↥(Xκ), (πκ).base x = (ιF).base q := by
  have hp : (p : ℕ).Prime := Fact.out
  have : (ιF).base q ∈ Set.range (πκ).base := by
    rw [Scheme.Pullback.range_fst]
    change (DRModel.toBase p).base ((ιF).base q) ∈ Set.range (gκ).base
    rw [← Scheme.Hom.comp_apply, TwoChartIntegralModel.ιFin_toBase]
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap _ ⊥ = Ideal.comap _ q.asIdeal
    haveI : (⊥ : Ideal κ).IsPrime := Ideal.isPrime_bot
    exact (comap_eq_span_of_natCast_mem p hp _ (⊥ : Ideal κ) (by simp)).trans
      (comap_eq_span_of_natCast_mem p hp _ q.asIdeal hq).symm
  exact this

def sheet (I : Ideal AA) : Set ↥(Xκ) :=
  ((πκ).base ⁻¹' ((ιF).base '' (PrimeSpectrum.zeroLocus (I : Set AA))ᶜ))ᶜ

theorem isClosed_sheet (I : Ideal AA) : IsClosed (sheet p κ I) := by
  rw [sheet, isClosed_compl_iff]
  exact ((ιF).isOpenEmbedding.isOpenMap _ (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl).preimage
    (πκ).continuous

theorem mem_sheet_iff (I : Ideal AA) (x : ↥(Xκ)) (q : PrimeSpectrum AA) (hq : (ιF).base q = (πκ).base x) :
    x ∈ sheet p κ I ↔ I ≤ q.asIdeal := by
  constructor
  · intro h
    by_contra hI
    apply h
    exact ⟨q, fun hmem => hI (SetLike.coe_subset_coe.mp ((PrimeSpectrum.mem_zeroLocus q _).mp hmem)), hq⟩
  · rintro hI ⟨q', hq', e⟩
    apply hq'
    obtain rfl : q = q' := (ιF).isOpenEmbedding.injective (hq.trans e.symm)
    exact (PrimeSpectrum.mem_zeroLocus q _).mpr (SetLike.coe_subset_coe.mpr hI)

theorem mem_sheet_of_not_mem_range (I : Ideal AA) (x : ↥(Xκ)) (hx : (πκ).base x ∉ Set.range (ιF).base) :
    x ∈ sheet p κ I := by
  simp only [sheet, Set.mem_compl_iff, Set.mem_preimage, Set.mem_image, not_exists, not_and]
  intro q _ e
  exact hx ⟨q, e⟩

theorem mem_sheet_or (𝔭₀ 𝔭₁ : Ideal AA) (hmin : (Ideal.span {((p : ℕ) : AA)}).minimalPrimes = {𝔭₀, 𝔭₁})
    (x : ↥(Xκ)) : x ∈ sheet p κ 𝔭₀ ∨ x ∈ sheet p κ 𝔭₁ := by
  by_cases hx : (πκ).base x ∈ Set.range (ιF).base
  · obtain ⟨q, hq⟩ := hx
    have hpq : ((p : ℕ) : AA) ∈ q.asIdeal := natCast_mem_of_base_eq p κ x q hq
    obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {((p : ℕ) : AA)}) (J := q.asIdeal)
      ((Ideal.span_singleton_le_iff_mem _).mpr hpq)
    rw [hmin] at hP
    rcases hP with rfl | rfl
    · exact Or.inl ((mem_sheet_iff p κ _ x q hq).mpr hPq)
    · exact Or.inr ((mem_sheet_iff p κ _ x q hq).mpr hPq)
  · exact Or.inl (mem_sheet_of_not_mem_range p κ _ x hx)

theorem exists_comp_subset_sheet (𝔛 : DRModelPackage p) [IsAlgClosed κ] (𝔭₀ 𝔭₁ : Ideal AA) [h₀ : 𝔭₀.IsPrime]
    [h₁ : 𝔭₁.IsPrime] (hmin : (Ideal.span {((p : ℕ) : AA)}).minimalPrimes = {𝔭₀, 𝔭₁}) (hne : 𝔭₀ ≠ 𝔭₁) :
    ∃ C D : (𝔛.ratModel κ).C ⟶ Xκ,
      ((C = 𝔛.compInf κ ∧ D = 𝔛.compZero κ) ∨ (C = 𝔛.compZero κ ∧ D = 𝔛.compInf κ)) ∧
      Set.range C.base ⊆ sheet p κ 𝔭₀ ∧ Set.range D.base ⊆ sheet p κ 𝔭₁ := by
  have key : ∀ Cc : (𝔛.ratModel κ).C ⟶ Xκ,
      Set.range Cc.base ⊆ sheet p κ 𝔭₀ ∨ Set.range Cc.base ⊆ sheet p κ 𝔭₁ := fun Cc =>
    (isPreirreducible_iff_isClosed_union_isClosed.mp (isPreirreducible_range Cc)) _ _ (isClosed_sheet p κ 𝔭₀)
      (isClosed_sheet p κ 𝔭₁) (fun x _ => mem_sheet_or p κ 𝔭₀ 𝔭₁ hmin x)
  have hm₀ : 𝔭₀ ∈ (Ideal.span {((p : ℕ) : AA)}).minimalPrimes := by rw [hmin]; exact Set.mem_insert _ _
  have hm₁ : 𝔭₁ ∈ (Ideal.span {((p : ℕ) : AA)}).minimalPrimes := by
    rw [hmin]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hm₀' : Minimal (fun q => q.IsPrime ∧ Ideal.span {((p : ℕ) : AA)} ≤ q) 𝔭₀ := hm₀
  have hm₁' : Minimal (fun q => q.IsPrime ∧ Ideal.span {((p : ℕ) : AA)} ≤ q) 𝔭₁ := hm₁
  have hp₀ : ((p : ℕ) : AA) ∈ 𝔭₀ := (Ideal.span_singleton_le_iff_mem _).mp hm₀'.1.2
  have hp₁ : ((p : ℕ) : AA) ∈ 𝔭₁ := (Ideal.span_singleton_le_iff_mem _).mp hm₁'.1.2
  have n₁₀ : ¬ 𝔭₁ ≤ 𝔭₀ := fun h => hne (le_antisymm (hm₀'.2 hm₁'.1 h) h)
  have n₀₁ : ¬ 𝔭₀ ≤ 𝔭₁ := fun h => hne (le_antisymm h (hm₁'.2 hm₀'.1 h))
  obtain ⟨x₀, hx₀⟩ := exists_base_eq p κ ⟨𝔭₀, h₀⟩ hp₀
  obtain ⟨x₁, hx₁⟩ := exists_base_eq p κ ⟨𝔭₁, h₁⟩ hp₁
  have hx₀' : x₀ ∉ sheet p κ 𝔭₁ := by rw [mem_sheet_iff p κ 𝔭₁ x₀ ⟨𝔭₀, h₀⟩ hx₀.symm]; exact n₁₀
  have hx₁' : x₁ ∉ sheet p κ 𝔭₀ := by rw [mem_sheet_iff p κ 𝔭₀ x₁ ⟨𝔭₁, h₁⟩ hx₁.symm]; exact n₀₁
  rcases 𝔛.comp_jointly_surjective κ x₀ with h0 | h0
  · have hC : Set.range (𝔛.compInf κ).base ⊆ sheet p κ 𝔭₀ := (key _).resolve_right fun h => hx₀' (h h0)
    have hx₁'' : x₁ ∈ Set.range (𝔛.compZero κ).base :=
      (𝔛.comp_jointly_surjective κ x₁).resolve_left fun h => hx₁' (hC h)
    have hD : Set.range (𝔛.compZero κ).base ⊆ sheet p κ 𝔭₁ := (key _).resolve_left fun h => hx₁' (h hx₁'')
    exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, hC, hD⟩
  · have hC : Set.range (𝔛.compZero κ).base ⊆ sheet p κ 𝔭₀ := (key _).resolve_right fun h => hx₀' (h h0)
    have hx₁'' : x₁ ∈ Set.range (𝔛.compInf κ).base :=
      (𝔛.comp_jointly_surjective κ x₁).resolve_right fun h => hx₁' (hC h)
    have hD : Set.range (𝔛.compInf κ).base ⊆ sheet p κ 𝔭₁ := (key _).resolve_left fun h => hx₁' (h hx₁'')
    exact ⟨_, _, Or.inr ⟨rfl, rfl⟩, hC, hD⟩

theorem germ_chartSection_mem_iff (x : ↥(Xκ)) (hx : (πκ).base x ∈ (ιF) ''ᵁ ⊤) (q : PrimeSpectrum AA)
    (hq : (ιF).base q = (πκ).base x) (t : AA) :
    ((Xκ).presheaf.germ (πκ ⁻¹ᵁ ((ιF) ''ᵁ ⊤)) x hx).hom
        (((πκ).app ((ιF) ''ᵁ ⊤)).hom (((ιF).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of AA)).inv t))) ∈ maximalIdeal _ ↔ t ∈ q.asIdeal := by
  rw [germ_app_mem_iff]
  have key : ∀ (z : ↥(DRModel p)) (hz : z ∈ (ιF) ''ᵁ ⊤), (ιF).base q = z →
      (((DRModel p).presheaf.germ ((ιF) ''ᵁ ⊤) z hz).hom (((ιF).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of AA)).inv t)) ∈ maximalIdeal _ ↔ t ∈ q.asIdeal) := by
    rintro z hz rfl
    exact germ_appIso_inv_mem_iff (CommRingCat.of AA) (ιF) q hz t
  exact key _ hx hq

theorem jCoordBC_eq_res :
    TwoChartIntegralModel.jCoordBC ℤ FF jF κ =
      ((TwoChartIntegralModel.baseChange ℤ FF jF κ).presheaf.map (homOfLE
        (show TwoChartIntegralModel.chartFinOpenBC ℤ FF jF κ ≤ πκ ⁻¹ᵁ ((ιF) ''ᵁ ⊤) from
          fun y hy => TwoChartIntegralModel.chartFinOpen_le_image_top ℤ FF jF hy)).op).hom
        (((πκ).app ((ιF) ''ᵁ ⊤)).hom (((ιF).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of AA)).inv (TwoChartIntegralModel.jChartFin ℤ FF jF)))) := by
  delta TwoChartIntegralModel.jCoordBC TwoChartIntegralModel.jCoord TwoChartIntegralModel.TwoChartsAux.f
    TwoChartIntegralModel.TwoChartsAux.sF TwoChartIntegralModel.baseChangeι
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

theorem germ_jCoordBC_eq (x : ↥(Xκ)) (hx : (πκ).base x ∈ (ιF) ''ᵁ ⊤)
    (hx' : x ∈ TwoChartIntegralModel.chartFinOpenBC ℤ FF jF κ) :
    ((TwoChartIntegralModel.baseChange ℤ FF jF κ).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ FF jF κ) x hx').hom
        (TwoChartIntegralModel.jCoordBC ℤ FF jF κ) =
      ((Xκ).presheaf.germ (πκ ⁻¹ᵁ ((ιF) ''ᵁ ⊤)) x hx).hom
        (((πκ).app ((ιF) ''ᵁ ⊤)).hom (((ιF).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of AA)).inv (TwoChartIntegralModel.jChartFin ℤ FF jF)))) := by
  rw [jCoordBC_eq_res p κ]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem germ_res_constSection_eq (x : ↥(Xκ)) (V : (TwoChartIntegralModel.baseChange ℤ FF jF κ).Opens) (hx : x ∈ V) (c : κ) :
    ((TwoChartIntegralModel.baseChange ℤ FF jF κ).presheaf.germ V x hx).hom
        ((TwoChartIntegralModel.baseChange ℤ FF jF κ).presheaf.map (homOfLE le_top).op
          (TwoChartIntegralModel.constSection ℤ FF jF κ c)) =
      ((TwoChartIntegralModel.baseChange ℤ FF jF κ).presheaf.germ ⊤ x trivial).hom
        (TwoChartIntegralModel.constSection ℤ FF jF κ c) :=
  TopCat.Presheaf.germ_res_apply _ _ _ _ _

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem jp_sub_jChartFin_pow_mem (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (𝔭₀ : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (e₀ : (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⧸ 𝔭₀) ≃+*
      Polynomial (ZMod p))
    (he₀j : e₀ (Ideal.Quotient.mk 𝔭₀
      (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = X)
    (he₀jp : e₀ (Ideal.Quotient.mk 𝔭₀ jp) = X ^ p) :
    jp - TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ^ p ∈ 𝔭₀ := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_sub, RingHom.map_pow]
  apply e₀.injective
  rw [RingEquiv.map_sub, RingEquiv.map_pow, he₀jp, he₀j, sub_self, RingEquiv.map_zero]

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem jChartFin_sub_jp_pow_mem (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (𝔭₁ : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (e₁ : (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⧸ 𝔭₁) ≃+*
      Polynomial (ZMod p))
    (he₁jp : e₁ (Ideal.Quotient.mk 𝔭₁ jp) = X)
    (he₁j : e₁ (Ideal.Quotient.mk 𝔭₁
      (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = X ^ p) :
    TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) - jp ^ p ∈ 𝔭₁ := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_sub, RingHom.map_pow]
  apply e₁.injective
  rw [RingEquiv.map_sub, RingEquiv.map_pow, he₁jp, he₁j, sub_self, RingEquiv.map_zero]

theorem carrier_eq_jp_sub_jChartFin_pow (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (ha : ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq - jq ^ p) :
    a = jp - TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ^ p := by
  apply Subtype.ext
  rw [Subalgebra.coe_sub, Subalgebra.coe_pow, TwoChartIntegralModel.coe_jChartFin]
  apply Subtype.ext
  have h1 : (((jp : ↥(modularFunctionFieldFull p)) - IgusaScheme.jFull p ^ p : ↥(modularFunctionFieldFull p)) :
      LaurentSeries ℚ) = ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) -
        ((IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) ^ p := by
    push_cast
    rfl
  rw [h1, ha, hjp, IgusaScheme.coe_jFull]

theorem carrier_mem (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (ha : ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq - jq ^ p)
    (𝔭₀ : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (e₀ : (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⧸ 𝔭₀) ≃+*
      Polynomial (ZMod p))
    (he₀j : e₀ (Ideal.Quotient.mk 𝔭₀
      (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = Polynomial.X)
    (he₀jp : e₀ (Ideal.Quotient.mk 𝔭₀ jp) = Polynomial.X ^ p) : a ∈ 𝔭₀ := by
  rw [carrier_eq_jp_sub_jChartFin_pow p jp hjp a ha]
  exact jp_sub_jChartFin_pow_mem p jp 𝔭₀ e₀ he₀j he₀jp

theorem exists_minimalPrimes_carrier (a : AA) (ha : ((a : FF) : LaurentSeries ℚ) = qExpand ℚ p jq - jq ^ p) :
    ∃ 𝔭₀ 𝔭₁ : Ideal AA, 𝔭₀.IsPrime ∧ 𝔭₁.IsPrime ∧
      (Ideal.span {((p : ℕ) : AA)}).minimalPrimes = {𝔭₀, 𝔭₁} ∧ 𝔭₀ ≠ 𝔭₁ ∧ a ∈ 𝔭₀ ∧
      ∃ jp : AA, a = jp - TwoChartIntegralModel.jChartFin ℤ FF jF ^ p ∧
        TwoChartIntegralModel.jChartFin ℤ FF jF - jp ^ p ∈ 𝔭₁ := by
  obtain ⟨jp, W₀, W₁, hjp, hp₀, hp₁, hW, hgen, hcomplete, ht, hres₀, hres₁⟩ :=
    ModularCurve.DRModel.exists_chartAlgFin_valuationSubring_pair_levelP p
  obtain ⟨𝔭₀, 𝔭₁, -, -, hmin, hne, ⟨e₀, he₀j, he₀jp⟩, ⟨e₁, he₁jp, he₁j⟩⟩ :=
    ModularCurve.DRModel.exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial p jp hjp W₀ W₁ hp₀ hp₁ hW hgen
      hcomplete ht hres₀ hres₁
  have hm₀ : 𝔭₀ ∈ (Ideal.span {((p : ℕ) : AA)}).minimalPrimes := by rw [hmin]; exact Set.mem_insert _ _
  have hm₁ : 𝔭₁ ∈ (Ideal.span {((p : ℕ) : AA)}).minimalPrimes := by
    rw [hmin]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  exact ⟨𝔭₀, 𝔭₁, Ideal.IsMinimalPrime.isPrime hm₀, Ideal.IsMinimalPrime.isPrime hm₁, hmin, hne,
    carrier_mem p jp hjp a ha 𝔭₀ e₀ he₀j he₀jp, jp, carrier_eq_jp_sub_jChartFin_pow p jp hjp a ha,
    jChartFin_sub_jp_pow_mem p jp 𝔭₁ e₁ he₁jp he₁j⟩

theorem clause_i (a : AA) (𝔭₀ : Ideal AA) (ha : a ∈ 𝔭₀) {Y : Scheme.{0}} (C : Y ⟶ Xκ)
    (hC : Set.range C.base ⊆ sheet p κ 𝔭₀) :
    (∀ y : ↥Y, ∀ hy : C.base y ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (C.base y) hy).hom
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _) := by
  intro y hy
  obtain ⟨q, -, hq⟩ := id hy
  exact (germ_chartSection_mem_iff p κ (C.base y) hy q hq a).mpr (((mem_sheet_iff p κ 𝔭₀ (C.base y) q hq).mp (hC ⟨y, rfl⟩)) ha)

theorem clause_ii [IsAlgClosed κ] (jp a : AA)
    (haA : a = jp - TwoChartIntegralModel.jChartFin ℤ FF jF ^ p) (𝔭₁ : Ideal AA)
    (hj : TwoChartIntegralModel.jChartFin ℤ FF jF - jp ^ p ∈ 𝔭₁) {Y : Scheme.{0}} (D : Y ⟶ Xκ)
    (hD : Set.range D.base ⊆ sheet p κ 𝔭₁) :
    (∀ y : ↥Y, ∀ hy : D.base y ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (D.base y) hy).hom
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _ →
        ∃ c : κ, c ^ (p ^ 2) = c ∧
          ∀ hy' : D.base y ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ,
            ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ
                (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ) (D.base y) hy').hom
              (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ -
                (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.map (homOfLE le_top).op
                  (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c)) ∈
              IsLocalRing.maximalIdeal _) := by
  have hpp : p.Prime := Fact.out
  intro y hy hgerm
  obtain ⟨q, -, hq⟩ := id hy
  have h𝔭₁q : 𝔭₁ ≤ q.asIdeal := (mem_sheet_iff p κ 𝔭₁ (D.base y) q hq).mp (hD ⟨y, rfl⟩)
  have haq : a ∈ q.asIdeal := (germ_chartSection_mem_iff p κ (D.base y) hy q hq a).mp hgerm

  let Bst := (Xκ).presheaf.stalk (D.base y)
  let φ : AA →+* ↑Bst :=
    ((Xκ).presheaf.germ (πκ ⁻¹ᵁ ((ιF) ''ᵁ ⊤)) (D.base y) hy).hom.comp
      (((πκ).app ((ιF) ''ᵁ ⊤)).hom.comp
        (((ιF).appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso (CommRingCat.of AA)).inv.hom))
  let ψ : κ →+* ↑Bst :=
    ((TwoChartIntegralModel.baseChange ℤ FF jF κ).presheaf.germ ⊤ (D.base y) trivial).hom.comp
      ((TwoChartIntegralModel.baseChangeToBase ℤ FF jF κ).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom)
  have hφ : ∀ t, φ t ∈ IsLocalRing.maximalIdeal ↑Bst ↔ t ∈ q.asIdeal := fun t =>
    germ_chartSection_mem_iff p κ (D.base y) hy q hq t
  have hψ : ∀ c : κ, ψ c = ((TwoChartIntegralModel.baseChange ℤ FF jF κ).presheaf.germ ⊤ (D.base y) trivial).hom
      (TwoChartIntegralModel.constSection ℤ FF jF κ c) := fun c => rfl
  obtain ⟨c, hc, hjc⟩ := exists_const_of_frobenius_pair p hpp φ ψ (TwoChartIntegralModel.jChartFin ℤ FF jF) jp
    ((hφ _).mpr (h𝔭₁q hj)) ((hφ _).mpr (haA ▸ haq))
  refine ⟨c, hc, fun hy' => ?_⟩
  rw [map_sub, germ_jCoordBC_eq p κ (D.base y) hy hy', germ_res_constSection_eq p κ (D.base y) _ hy' c, ← hψ c]
  exact hjc

end Concrete

end ModularCurve.DRModelPackage.HorPkg

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]

    (a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (ha : ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq - jq ^ p) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ (C D : (𝔛.ratModel κ).C ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))),
      ((C = 𝔛.compInf κ ∧ D = 𝔛.compZero κ) ∨ (C = 𝔛.compZero κ ∧ D = 𝔛.compInf κ)) ∧

      (∀ y : ↥(𝔛.ratModel κ).C, ∀ hy : C.base y ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (C.base y) hy).hom
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _) ∧

      (∀ y : ↥(𝔛.ratModel κ).C, ∀ hy : D.base y ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (D.base y) hy).hom
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _ →
        ∃ c : κ, c ^ (p ^ 2) = c ∧
          ∀ hy' : D.base y ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ,
            ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ
                (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ) (D.base y) hy').hom
              (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ -
                (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.map (homOfLE le_top).op
                  (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c)) ∈
              IsLocalRing.maximalIdeal _) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨𝔭₀, 𝔭₁, h₀, h₁, hmin, hne, ha𝔭₀, jp, haA, hj𝔭₁⟩ :=
    ModularCurve.DRModelPackage.HorPkg.exists_minimalPrimes_carrier p a ha
  obtain ⟨C, D, hCD, hC, hD⟩ :=
    ModularCurve.DRModelPackage.HorPkg.exists_comp_subset_sheet p κ 𝔛 𝔭₀ 𝔭₁ hmin hne
  refine ⟨C, D, hCD, ?_, ?_⟩
  · exact ModularCurve.DRModelPackage.HorPkg.clause_i p κ a 𝔭₀ ha𝔭₀ C hC
  · exact ModularCurve.DRModelPackage.HorPkg.clause_ii p κ jp a haA 𝔭₁ hj𝔭₁ D hD

end S_ModularCurve_DRModelPackage_exists_range_comp_subset_zeroLocus_jq_sub_pow
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_exists_range_comp_subset_zeroLocus_jq_sub_pow (solution)

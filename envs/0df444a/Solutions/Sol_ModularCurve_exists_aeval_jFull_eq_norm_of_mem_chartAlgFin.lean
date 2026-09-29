-- Prove2me | solution 1 for ModularCurve.exists_aeval_jFull_eq_norm_of_mem_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/eff6b2dd-b3ec-5d21-8b23-fee65a1446f9

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_P2M_Dup_ModularCurve_transcendental_jqNModC
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_aeval_jFull_eq_norm_of_mem_chartAlgFin
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

p2m_open "ModularCurve~transcendental_jq P2MW.S_ModularCurve_exists_aeval_jFull_eq_norm_of_mem_chartAlgFin.ModularCurve Polynomial IntermediateField"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme.jFull IgusaScheme jq jqN_one modularFunctionFieldFull transcendental_jqNModC finiteDimensional_adjoin_jFull_modularFunctionFieldFull jqNModC_rat"
namespace CU2
p2m_open "ModularCurve~transcendental_jq"

variable (p : ℕ) [Fact p.Prime] [NeZero p]

abbrev F : Type := ↥(modularFunctionFieldFull p)

abbrev jF : F p := IgusaScheme.jFull p

abbrev Zj : Subalgebra ℤ (F p) := Algebra.adjoin ℤ ({jF p} : Set (F p))

abbrev K : IntermediateField ℚ (F p) := IntermediateField.adjoin ℚ ({jF p} : Set (F p))

scoped instance instIsScalarTowerRatLaurent : IsScalarTower ℚ ℚ (LaurentSeries ℚ) := ⟨fun a b c => mul_smul a b c⟩

p2m_attr_erase "instance" "Algebra.instCommRingAdjoinSingleton"

theorem transcendental_jq : Transcendental ℚ jq := by
  have h := ModularCurve.transcendental_jqNModC ℚ 1
  rwa [jqNModC_rat, jqN_one] at h

set_option synthInstance.maxHeartbeats 1600000 in
theorem transcendental_jF : Transcendental ℚ (jF p) := by
  intro halg
  apply transcendental_jq
  obtain ⟨P, hP0, hP⟩ := halg
  refine ⟨P, hP0, ?_⟩

  let ι : F p →+* LaurentSeries ℚ := SubringClass.subtype (modularFunctionFieldFull p)
  have h := congrArg ι hP
  rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂] at h
  have hring : ι.comp (algebraMap ℚ (F p)) = algebraMap ℚ (LaurentSeries ℚ) := RingHom.ext_rat _ _
  rw [hring] at h
  rw [Polynomial.aeval_def]
  exact h

theorem aeval_int_injective : Function.Injective (Polynomial.aeval (R := ℤ) (jF p)) := by
  intro P Q hPQ
  have hq : Function.Injective (Polynomial.aeval (R := ℚ) (jF p)) :=
    (transcendental_iff_injective).mp (transcendental_jF p)
  have : Polynomial.aeval (R := ℚ) (jF p) (P.map (Int.castRingHom ℚ)) =
      Polynomial.aeval (R := ℚ) (jF p) (Q.map (Int.castRingHom ℚ)) := by
    have e : (algebraMap ℚ (F p)).comp (Int.castRingHom ℚ) = algebraMap ℤ (F p) := RingHom.ext_int _ _
    simpa only [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def, Polynomial.eval₂_map,
      ← Polynomial.eval₂_eq_eval_map, e] using hPQ
  exact Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective (hq this)

set_option synthInstance.maxHeartbeats 1600000 in
scoped instance instIsDomainZj : IsDomain (Zj p) := inferInstance
set_option synthInstance.maxHeartbeats 1600000 in
scoped instance instAlgebraZjF : Algebra (Zj p) (F p) := inferInstance
set_option synthInstance.maxHeartbeats 1600000 in
scoped instance instIsScalarTowerZj : IsScalarTower (Zj p) (F p) (F p) := inferInstance

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_isIntegral_coeff_zero_minpoly_eq_mul (x : F p) (hx : IsIntegral (Zj p) x) :
    ∃ c : F p, IsIntegral (Zj p) c ∧ algebraMap (Zj p) (F p) ((minpoly (Zj p) x).coeff 0) = c * x := by
  classical

  have heval : Polynomial.aeval x (minpoly (Zj p) x).divX * x +
      algebraMap (Zj p) (F p) ((minpoly (Zj p) x).coeff 0) = 0 := by
    have h := minpoly.aeval (Zj p) x
    conv_lhs at h => rw [← Polynomial.divX_mul_X_add (minpoly (Zj p) x)]
    simpa only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] using h
  refine ⟨-Polynomial.aeval x (minpoly (Zj p) x).divX, ?_, ?_⟩
  ·
    refine IsIntegral.neg ?_
    rw [Polynomial.aeval_eq_sum_range]
    refine IsIntegral.sum _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact isIntegral_algebraMap.mul (hx.pow i)
  · linear_combination (exp := 1) heval

theorem adjoin_int_le_K : ∀ z : F p, z ∈ Zj p → z ∈ K p := by
  intro z hz
  refine Algebra.adjoin_le (S := ((K p).toSubalgebra.restrictScalars ℤ)) ?_ hz
  rintro _ rfl
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)

def inclZjK : Zj p →+* K p where
  toFun z := ⟨z.1, adjoin_int_le_K p z.1 z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

scoped instance instAlgebraZjK : Algebra (Zj p) (K p) := (inclZjK p).toAlgebra

theorem algebraMap_ZjK_apply (z : Zj p) : ((algebraMap (Zj p) (K p) z : K p) : F p) = (z : F p) := rfl

set_option synthInstance.maxHeartbeats 1600000 in
scoped instance instIsScalarTowerZjKF : IsScalarTower (Zj p) (K p) (F p) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

set_option synthInstance.maxHeartbeats 1600000 in
scoped instance instFaithfulSMulZjK : FaithfulSMul (Zj p) (K p) :=
  (faithfulSMul_iff_algebraMap_injective (Zj p) (K p)).mpr fun a b h =>
    Subtype.ext (by simpa [algebraMap_ZjK_apply] using congrArg (Subtype.val : K p → F p) h)

theorem transcendental_int_jF : Transcendental ℤ (jF p) := fun h =>
  transcendental_jF p (h.extendScalars (algebraMap ℤ ℚ).injective_int)

set_option synthInstance.maxHeartbeats 1600000 in
scoped instance instIsIntegrallyClosedZj : IsIntegrallyClosed (Zj p) :=
  IsIntegrallyClosed.of_equiv (Polynomial.algEquivOfTranscendental ℤ (jF p) (transcendental_int_jF p)).toRingEquiv

theorem aeval_int_eq_aeval_map (R : Polynomial ℤ) :
    (Polynomial.aeval (jF p) R : F p) = Polynomial.aeval (jF p) (R.map (Int.castRingHom ℚ)) := by
  rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, Polynomial.aeval_map_algebraMap]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

scoped instance instIsFractionRingZjK : IsFractionRing (Zj p) (K p) := by
  classical
  refine IsFractionRing.of_field (Zj p) (K p) ?_
  rintro ⟨z, hz⟩
  obtain ⟨r, hr, s, hs, hzrs⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hr hs
  obtain ⟨P, rfl⟩ := hr
  obtain ⟨Q, rfl⟩ := hs
  obtain ⟨b, hb, hP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (S := ℚ) P
  obtain ⟨b', hb', hQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (S := ℚ) Q
  set P' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (S := ℚ) P with hP'def
  set Q' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (S := ℚ) Q with hQ'def
  have hb0 : (b : F p) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hb
  have hb0' : (b' : F p) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hb'

  rw [Algebra.smul_def, Polynomial.algebraMap_apply] at hP hQ
  have hP'' : (Polynomial.aeval (jF p) P' : F p) = (b : F p) * Polynomial.aeval (jF p) P := by
    rw [aeval_int_eq_aeval_map, show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hP, map_mul, Polynomial.aeval_C]
    simp
  have hQ'' : (Polynomial.aeval (jF p) Q' : F p) = (b' : F p) * Polynomial.aeval (jF p) Q := by
    rw [aeval_int_eq_aeval_map, show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hQ, map_mul, Polynomial.aeval_C]
    simp
  refine ⟨⟨Polynomial.aeval (jF p) (Polynomial.C b' * P'), Polynomial.aeval_mem_adjoin_singleton _ _⟩,
          ⟨Polynomial.aeval (jF p) (Polynomial.C b * Q'), Polynomial.aeval_mem_adjoin_singleton _ _⟩, ?_⟩
  apply Subtype.ext
  change z = ((Polynomial.aeval (jF p) (Polynomial.C b' * P') : F p)) / (Polynomial.aeval (jF p) (Polynomial.C b * Q') : F p)
  rw [hzrs, map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, hP'', hQ'', algebraMap_int_eq,
    eq_intCast, eq_intCast,
    show (b' : F p) * ((b : F p) * Polynomial.aeval (jF p) P) = ((b : F p) * (b' : F p)) * Polynomial.aeval (jF p) P by ring,
    show (b : F p) * ((b' : F p) * Polynomial.aeval (jF p) Q) = ((b : F p) * (b' : F p)) * Polynomial.aeval (jF p) Q by ring,
    mul_div_mul_left _ _ (mul_ne_zero hb0 hb0')]

scoped instance instFiniteDimensionalKF : FiniteDimensional (K p) (F p) :=
  ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull p

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem exists_int_poly_aeval_eq_norm_and_eq_mul (x : F p) (hx : IsIntegral (Zj p) x) :
    ∃ (N : Polynomial ℤ) (c : F p), IsIntegral (Zj p) c ∧
      (Polynomial.aeval (jF p) N : F p) = algebraMap (K p) (F p) (Algebra.norm (K p) x) ∧
      (Polynomial.aeval (jF p) N : F p) = c * x := by
  classical
  have hmin : minpoly (K p) x = (minpoly (Zj p) x).map (algebraMap (Zj p) (K p)) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (K p) hx
  have hxK : IsIntegral (K p) x := hx.tower_top
  set r := Module.finrank (↥(K p))⟮x⟯ (F p) with hr_def
  set d := (minpoly (K p) x).natDegree with hd_def
  have hnorm : Algebra.norm (K p) x = ((-1) ^ d * (minpoly (K p) x).coeff 0) ^ r := by
    rw [Algebra.norm_eq_norm_adjoin (K p) x]
    congr 1
    have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hxK)
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
      IntermediateField.minpoly_gen] at h
    exact h
  set a₀ : Zj p := (minpoly (Zj p) x).coeff 0 with ha₀_def
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Polynomial ℤ, (Polynomial.aeval (jF p) A₀ : F p) = (a₀ : F p) := by
    have h : (a₀ : F p) ∈ (Polynomial.aeval (jF p) : Polynomial ℤ →ₐ[ℤ] F p).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact a₀.2
    rwa [AlgHom.mem_range] at h
  obtain ⟨c₁, hc₁, hc₁x⟩ := exists_isIntegral_coeff_zero_minpoly_eq_mul p x hx
  have hr1 : 1 ≤ r := Module.finrank_pos
  have hcoeff : ((minpoly (K p) x).coeff 0 : F p) = (a₀ : F p) := by
    rw [hmin, Polynomial.coeff_map]; rfl
  refine ⟨(Polynomial.C ((-1) ^ d) * A₀) ^ r, ((-1 : F p) ^ d) ^ r * (a₀ : F p) ^ (r - 1) * c₁, ?_, ?_, ?_⟩
  · refine IsIntegral.mul (IsIntegral.mul ((isIntegral_one.neg).pow d |>.pow r) ?_) hc₁
    exact (isIntegral_algebraMap (R := Zj p) (x := a₀)).pow _
  · rw [hnorm]
    simp only [map_pow, map_mul, map_neg, map_one, hA₀, IntermediateField.algebraMap_apply]
    rw [hcoeff]
  · rw [map_pow, map_mul, Polynomial.aeval_C, hA₀]
    have : (a₀ : F p) = c₁ * x := hc₁x
    obtain ⟨r', hr'⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [hr', Nat.add_sub_cancel, pow_succ, mul_pow]
    nth_rewrite 2 [this]
    simp only [eq_intCast, Int.cast_pow, Int.cast_neg, Int.cast_one]
    ring

end ModularCurve.CU2
p2m_reactivate "P2MW.S_ModularCurve_exists_aeval_jFull_eq_norm_of_mem_chartAlgFin.ModularCurve P2MW.S_ModularCurve_exists_aeval_jFull_eq_norm_of_mem_chartAlgFin.ModularCurve.CU2"
p2m_reactivate "P2MW.S_ModularCurve_exists_aeval_jFull_eq_norm_of_mem_chartAlgFin.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_aeval_jFull_eq_norm_of_mem_chartAlgFin.ModularCurve P2MW.S_ModularCurve_exists_aeval_jFull_eq_norm_of_mem_chartAlgFin.ModularCurve.CU2"

open ModularCurve.CU2 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (y : ↥(ModularCurve.modularFunctionFieldFull p))
    (hy : y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (IgusaScheme.jFull p)) :
    ∃ M : Polynomial ℤ,
      (Polynomial.aeval (IgusaScheme.jFull p) M : ↥(ModularCurve.modularFunctionFieldFull p)) =
        algebraMap ↥(IntermediateField.adjoin ℚ ({IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p))) ↥(ModularCurve.modularFunctionFieldFull p)
          (Algebra.norm ↥(IntermediateField.adjoin ℚ ({IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p))) y) := by
  have hx : IsIntegral (Zj p) y := (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff ℤ (F p)).mp hy
  obtain ⟨N, c, -, hN, -⟩ := exists_int_poly_aeval_eq_norm_and_eq_mul p y hx
  exact ⟨N, hN⟩

end S_ModularCurve_exists_aeval_jFull_eq_norm_of_mem_chartAlgFin
end P2MW
export P2MW.S_ModularCurve_exists_aeval_jFull_eq_norm_of_mem_chartAlgFin (solution)

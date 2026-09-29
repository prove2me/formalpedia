-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.finite_levelRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/4d23bb09-18a4-58d2-bf3f-f21255307ba1

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_HpoolLevelRing
import Theorems.Thm_Module_Finite_quotient_of_isUnit_leadingCoeff_of_mem
import Theorems.Thm_ModularCurve_exists_int_poly_natDegree_aeval_jFull_eq_mul_aeval_modularUnitSeries
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_finite_levelRing
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false

open Polynomial

noncomputable section

namespace LevelBC

variable (A : Type) [CommRing A] (c d : ℤ) (u : A) (g : ℤ[X])

abbrev Aaway (r : ℤ) : Type := Localization.Away (algebraMap ℤ A r)

abbrev Br (r : ℤ) : Type := Aaway A r ⧸ Ideal.span {aeval (algebraMap A (Aaway A r) u) g}

scoped instance algAway (r : ℤ) : Algebra (Localization.Away r) (Aaway A r) := (Localization.awayMap (algebraMap ℤ A) r).toAlgebra

scoped instance algAwayBr (r : ℤ) : Algebra (Localization.Away r) (Br A u g r) := Ideal.Quotient.algebra _

theorem ringHom_away_ext {r : ℤ} {X : Type*} [CommRing X] (f₁ f₂ : Localization.Away r →+* X) : f₁ = f₂ :=
  IsLocalization.ringHom_ext (Submonoid.powers r) (Subsingleton.elim _ _)

section maps

noncomputable def φA : Aaway A c →+* Aaway A (c * d) :=
  IsLocalization.Away.lift (algebraMap ℤ A c) (S := Aaway A c)
    (isUnit_of_dvd_unit (map_dvd (algebraMap A (Aaway A (c * d))) (map_dvd (algebraMap ℤ A) (dvd_mul_right c d)))
      (IsLocalization.Away.algebraMap_isUnit (algebraMap ℤ A (c * d))))

theorem φA_algebraMap (a : A) : φA A c d (algebraMap A _ a) = algebraMap A _ a :=
  IsLocalization.Away.lift_eq _ _ a

end maps

section instances

noncomputable scoped instance algAA : Algebra (Aaway A c) (Aaway A (c * d)) := (φA A c d).toAlgebra

noncomputable scoped instance algRR : Algebra (Localization.Away c) (Localization.Away (c * d)) := algAA ℤ c d

scoped instance istAAA : IsScalarTower A (Aaway A c) (Aaway A (c * d)) :=
  IsScalarTower.of_algebraMap_eq (fun a => (φA_algebraMap A c d a).symm)

noncomputable scoped instance algRA' : Algebra (Localization.Away c) (Aaway A (c * d)) :=
  ((algebraMap (Localization.Away (c * d)) (Aaway A (c * d))).comp
    (algebraMap (Localization.Away c) (Localization.Away (c * d)))).toAlgebra

scoped instance istRAA : IsScalarTower (Localization.Away c) (Aaway A c) (Aaway A (c * d)) :=
  IsScalarTower.of_algebraMap_eq' (ringHom_away_ext _ _)

scoped instance istRRA : IsScalarTower (Localization.Away c) (Localization.Away (c * d)) (Aaway A (c * d)) :=
  IsScalarTower.of_algebraMap_eq' (ringHom_away_ext _ _)

scoped instance isLocA : IsLocalization.Away (algebraMap ℤ (Aaway A c) d) (Aaway A (c * d)) := by
  classical

  have hzc : algebraMap ℤ (Aaway A c) d = algebraMap A (Aaway A c) (algebraMap ℤ A d) :=
    RingHom.congr_fun (Subsingleton.elim (algebraMap ℤ (Aaway A c)) ((algebraMap A (Aaway A c)).comp (algebraMap ℤ A))) d
  rw [IsLocalization.Away, hzc]
  set x : A := algebraMap ℤ A c with hx
  set y : A := algebraMap ℤ A d with hy
  set φ : A →+* Aaway A c := algebraMap A (Aaway A c) with hφ

  have h0 : IsLocalization (Submonoid.powers (x * y)) (Aaway A (c * d)) := by
    have : x * y = algebraMap ℤ A (c * d) := (map_mul (algebraMap ℤ A) c d).symm
    rw [this]; exact Localization.isLocalization

  set N : Submonoid A := Submonoid.powers x ⊔ Submonoid.powers y with hN
  have h1 : IsLocalization N (Aaway A (c * d)) := by
    refine @IsLocalization.of_le_of_exists_dvd A _ (Submonoid.powers (x * y)) (Aaway A (c * d)) _ _ h0 N ?_ ?_
    · rintro _ ⟨n, rfl⟩
      show (x * y) ^ n ∈ N
      rw [mul_pow]
      exact Submonoid.mul_mem_sup ⟨n, rfl⟩ ⟨n, rfl⟩
    · intro n hn
      obtain ⟨a, ha, b, hb, rfl⟩ := Submonoid.mem_sup.1 hn
      obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ha
      obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hb
      refine ⟨(x * y) ^ (i + j), ⟨i + j, rfl⟩, ?_⟩
      rw [mul_pow, pow_add, pow_add]
      exact mul_dvd_mul (dvd_mul_right _ _) (dvd_mul_left _ _)

  have h2 : IsLocalization (N.map φ) (Aaway A (c * d)) :=
    haveI := h1
    IsLocalization.isLocalization_of_submonoid_le (S := Aaway A c) (T := Aaway A (c * d)) (Submonoid.powers x) N le_sup_left

  have hNmap : N.map φ = Submonoid.powers (φ x) ⊔ Submonoid.powers (φ y) := by
    rw [hN, Submonoid.map_sup, Submonoid.map_powers, Submonoid.map_powers]
  have hux : IsUnit (φ x) := IsLocalization.Away.algebraMap_isUnit x
  refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers (φ y)) (N.map φ) ?_ ?_).mpr h2
  · rw [hNmap]; exact le_sup_right
  · intro n hn
    rw [hNmap] at hn
    obtain ⟨a, ha, b, hb, rfl⟩ := Submonoid.mem_sup.1 hn
    obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ha
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hb
    exact ⟨φ y ^ j, ⟨j, rfl⟩, ((hux.pow i).mul_left_dvd).2 dvd_rfl⟩

scoped instance isLocR : IsLocalization.Away (algebraMap ℤ (Localization.Away c) d) (Localization.Away (c * d)) :=
  isLocA ℤ c d

end instances

section quotient

theorem algebraMap_aeval_eq :
    algebraMap (Aaway A c) (Aaway A (c * d)) (aeval (algebraMap A (Aaway A c) u) g) =
      aeval (algebraMap A (Aaway A (c * d)) u) g := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_apply A]
  congr 1
  exact Subsingleton.elim _ _

theorem map_ideal_eq :
    (Ideal.span {aeval (algebraMap A (Aaway A c) u) g}).map (algebraMap (Aaway A c) (Aaway A (c * d))) =
      Ideal.span {aeval (algebraMap A (Aaway A (c * d)) u) g} := by
  rw [Ideal.map_span, Set.image_singleton, algebraMap_aeval_eq]

theorem ideal_le_comap :
    Ideal.span {aeval (algebraMap A (Aaway A c) u) g} ≤
      (Ideal.span {aeval (algebraMap A (Aaway A (c * d)) u) g}).comap (algebraMap (Aaway A c) (Aaway A (c * d))) := by
  rw [← Ideal.map_le_iff_le_comap, map_ideal_eq]

noncomputable scoped instance algBB : Algebra (Br A u g c) (Br A u g (c * d)) :=
  (Ideal.quotientMap _ (algebraMap (Aaway A c) (Aaway A (c * d))) (ideal_le_comap A c d u g)).toAlgebra

scoped instance istRRB : @IsScalarTower (Localization.Away c) (Localization.Away (c * d)) (Br A u g (c * d))
    Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  @IsScalarTower.of_algebraMap_eq' (Localization.Away c) (Localization.Away (c * d)) (Br A u g (c * d)) _ _ _ _ _ _
    (ringHom_away_ext _ _)

scoped instance istRBB' : @IsScalarTower (Localization.Away c) (Br A u g c) (Br A u g (c * d))
    Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  @IsScalarTower.of_algebraMap_eq' (Localization.Away c) (Br A u g c) (Br A u g (c * d)) _ _ _ _ _ _
    (ringHom_away_ext _ _)

scoped instance isLocB : IsLocalization ((Submonoid.powers (algebraMap ℤ (Aaway A c) d)).map
    (Ideal.Quotient.mk (Ideal.span {aeval (algebraMap A (Aaway A c) u) g}))) (Br A u g (c * d)) :=
  IsLocalization.of_surjective (Submonoid.powers (algebraMap ℤ (Aaway A c) d)) (Aaway A (c * d))
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    rfl (by rw [Ideal.mk_ker, Ideal.mk_ker, map_ideal_eq])

theorem submonoid_eq :
    Algebra.algebraMapSubmonoid (Br A u g c) (Submonoid.powers (algebraMap ℤ (Localization.Away c) d)) =
      (Submonoid.powers (algebraMap ℤ (Aaway A c) d)).map
        (Ideal.Quotient.mk (Ideal.span {aeval (algebraMap A (Aaway A c) u) g})) := by
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, Submonoid.map_powers]
  congr 1
  exact RingHom.congr_fun (Subsingleton.elim ((algebraMap _ (Br A u g c)).comp (algebraMap ℤ (Localization.Away c)))
    ((Ideal.Quotient.mk _).comp (algebraMap ℤ (Aaway A c)))) d

scoped instance isPushoutB : Algebra.IsPushout (Localization.Away c) (Br A u g c) (Localization.Away (c * d)) (Br A u g (c * d)) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (Br A u g c) (Submonoid.powers (algebraMap ℤ (Localization.Away c) d)))
      (Br A u g (c * d)) := by rw [submonoid_eq]; exact isLocB A c d u g
  exact Algebra.isPushout_of_isLocalization (Submonoid.powers (algebraMap ℤ (Localization.Away c) d))
    (Localization.Away (c * d)) (Br A u g c) (Br A u g (c * d))

end quotient

section transfer

scoped instance isPIR (r : ℤ) : IsPrincipalIdealRing (Localization.Away r) where
  principal I := by
    obtain ⟨n, hn⟩ := (IsPrincipalIdealRing.principal (I.under ℤ)).principal
    refine ⟨⟨algebraMap ℤ _ n, ?_⟩⟩
    rw [← IsLocalization.map_under (Submonoid.powers r) (Localization.Away r) I, hn, Ideal.submodule_span_eq,
      Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]

theorem isDomain_away {r : ℤ} (hr : r ≠ 0) : IsDomain (Localization.Away r) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr)

variable {A c d u g}

theorem transfer (hcd : c * d ≠ 0) (n : ℕ)
    (hfin : Module.Finite (Localization.Away c) (Br A u g c))
    (het : Algebra.Etale (Localization.Away c) (Br A u g c))
    (hrk : ∀ 𝔮 : PrimeSpectrum (Localization.Away c), Module.rankAtStalk (R := Localization.Away c) (Br A u g c) 𝔮 = n) :
    Module.Finite (Localization.Away (c * d)) (Br A u g (c * d)) ∧
    Algebra.Etale (Localization.Away (c * d)) (Br A u g (c * d)) ∧
    Module.Free (Localization.Away (c * d)) (Br A u g (c * d)) ∧
    Module.finrank (Localization.Away (c * d)) (Br A u g (c * d)) = n ∧
    ∀ 𝔮 : PrimeSpectrum (Localization.Away (c * d)),
      Module.rankAtStalk (R := Localization.Away (c * d)) (Br A u g (c * d)) 𝔮 = n := by
  haveI := hfin; haveI := het
  haveI : Algebra.IsPushout (Localization.Away c) (Localization.Away (c * d)) (Br A u g c) (Br A u g (c * d)) :=
    Algebra.IsPushout.symm inferInstance
  let e : TensorProduct (Localization.Away c) (Localization.Away (c * d)) (Br A u g c) ≃ₐ[Localization.Away (c * d)]
      Br A u g (c * d) :=
    Algebra.IsPushout.equiv (Localization.Away c) (Localization.Away (c * d)) (Br A u g c) (Br A u g (c * d))
  have hfin' : Module.Finite (Localization.Away (c * d)) (Br A u g (c * d)) := Module.Finite.equiv e.toLinearEquiv
  have het' : Algebra.Etale (Localization.Away (c * d)) (Br A u g (c * d)) := by
    have hloc : IsLocalization ((Submonoid.powers (algebraMap ℤ (Localization.Away c) d)).map
        (algebraMap (Localization.Away c) (Br A u g c))) (Br A u g (c * d)) := by
      rw [← Algebra.algebraMapSubmonoid, submonoid_eq]; exact isLocB A c d u g
    have hfe : Algebra.FormallyEtale (Localization.Away (c * d)) (Br A u g (c * d)) :=
      Algebra.FormallyEtale.localization_map (R := Localization.Away c) (S := Br A u g c)
        (Rₘ := Localization.Away (c * d)) (Sₘ := Br A u g (c * d))
        (Submonoid.powers (algebraMap ℤ (Localization.Away c) d))
    haveI := hfin'
    have hfp : Algebra.FinitePresentation (Localization.Away (c * d)) (Br A u g (c * d)) :=
      (Algebra.FinitePresentation.of_finiteType (R := Localization.Away (c * d)) (A := Br A u g (c * d))).mp inferInstance
    exact ⟨hfe, hfp⟩
  have hrk' : ∀ 𝔮 : PrimeSpectrum (Localization.Away (c * d)),
      Module.rankAtStalk (R := Localization.Away (c * d)) (Br A u g (c * d)) 𝔮 = n := fun 𝔮 => by
    rw [Algebra.rankAtStalk_eq_of_isPushout (Localization.Away c) (Br A u g c) (Localization.Away (c * d)) (Br A u g (c * d)) 𝔮]
    exact hrk _
  haveI := hfin'; haveI := het'
  haveI : IsDomain (Localization.Away (c * d)) := isDomain_away hcd
  haveI : Module.Free (Localization.Away (c * d)) (Br A u g (c * d)) := inferInstance
  refine ⟨hfin', het', inferInstance, ?_, hrk'⟩
  have h := Module.rankAtStalk_eq_finrank_of_free (R := Localization.Away (c * d)) (M := Br A u g (c * d))
  have := hrk' ⟨⊥, Ideal.isPrime_bot⟩
  rw [h] at this
  exact this

end transfer

section finite_of_norm

theorem finite_quotient_of_norm {A : Type} [CommRing A] (R A' : Type) [CommRing R] [CommRing A'] [Algebra ℤ R]
    [Algebra ℤ A'] [Algebra R A'] [Algebra A A'] (c : ℤ) [IsLocalization.Away c R]
    [IsLocalization.Away (algebraMap ℤ A c) A']
    [Nontrivial R] (j u : A) (g N : ℤ[X]) (c' : A)
    (hfinA : letI : Algebra ℤ[X] A := (Polynomial.aeval j).toRingHom.toAlgebra; Module.Finite ℤ[X] A)
    (hN : Polynomial.aeval j N = c' * Polynomial.aeval u g)
    (hlc : IsUnit (algebraMap ℤ R N.leadingCoeff)) :
    Module.Finite R (A' ⧸ Ideal.span {Polynomial.aeval (algebraMap A A' u) g}) := by

  letI algZA : Algebra ℤ[X] A := (Polynomial.aeval j).toRingHom.toAlgebra
  haveI : Module.Finite ℤ[X] A := hfinA
  letI algZXA : Algebra ℤ[X] A' := ((algebraMap A A').comp (algebraMap ℤ[X] A)).toAlgebra
  letI algRXA : Algebra R[X] A' := (Polynomial.aeval (R := R) (algebraMap A A' j)).toRingHom.toAlgebra
  letI algZXRX : Algebra ℤ[X] R[X] := Polynomial.algebra ℤ R
  haveI : IsScalarTower ℤ[X] A A' := IsScalarTower.of_algebraMap_eq' rfl
  haveI istZAA : @IsScalarTower ℤ A A' Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hZXA : ∀ q : ℤ[X], algebraMap ℤ[X] A q = Polynomial.aeval j q := fun _ => rfl
  have hRXA : ∀ q : R[X], algebraMap R[X] A' q = Polynomial.aeval (algebraMap A A' j) q := fun _ => rfl
  haveI : IsScalarTower R R[X] A' :=
    IsScalarTower.of_algebraMap_eq' (Polynomial.aeval (R := R) (algebraMap A A' j)).comp_algebraMap.symm
  haveI : IsScalarTower ℤ[X] R[X] A' := by
    refine IsScalarTower.of_algebraMap_eq' (Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_)
    rw [RingHom.comp_apply, Polynomial.algebraMap_def, Polynomial.coe_mapRingHom, Polynomial.map_X, hRXA,
      Polynomial.aeval_X, IsScalarTower.algebraMap_apply ℤ[X] A A', hZXA, Polynomial.aeval_X]

  haveI : IsLocalization (Algebra.algebraMapSubmonoid A ((Submonoid.powers c).map (C : ℤ →+* ℤ[X]))) A' := by
    have h : Algebra.algebraMapSubmonoid A ((Submonoid.powers c).map (C : ℤ →+* ℤ[X])) =
        Submonoid.powers (algebraMap ℤ A c) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, Submonoid.map_powers]
      congr 1
      show algebraMap ℤ[X] A (C c) = algebraMap ℤ A c
      rw [hZXA, Polynomial.aeval_C]
    rw [h]; infer_instance
  haveI : IsLocalization ((Submonoid.powers c).map (C : ℤ →+* ℤ[X])) R[X] :=
    Polynomial.isLocalization (Submonoid.powers c) R
  haveI : Module.Finite R[X] A' :=
    Module.Finite.of_isLocalization ℤ[X] A ((Submonoid.powers c).map (C : ℤ →+* ℤ[X]))

  have hmapN : algebraMap R[X] A' (N.map (algebraMap ℤ R)) = algebraMap A A' (Polynomial.aeval j N) := by
    rw [hRXA, Polynomial.aeval_def, Polynomial.eval₂_map,
      Subsingleton.elim ((algebraMap R A').comp (algebraMap ℤ R)) (algebraMap ℤ A'), ← Polynomial.aeval_def,
      Polynomial.aeval_algebraMap_apply]

  refine Module.Finite.quotient_of_isUnit_leadingCoeff_of_mem R A' (N.map (algebraMap ℤ R)) ?_ _ ?_
  · rwa [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (algebraMap ℤ R) hlc.ne_zero]
  · rw [hmapN, hN, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Polynomial.aeval_algebraMap_apply A' u g).symm)

theorem finite_of_norm {A : Type} [CommRing A] [IsDomain A] (j u : A) (g N : ℤ[X]) (c' : A) (c : ℤ) (hc : c ≠ 0)
    (hfinA : letI : Algebra ℤ[X] A := (Polynomial.aeval j).toRingHom.toAlgebra; Module.Finite ℤ[X] A)
    (hN : Polynomial.aeval j N = c' * Polynomial.aeval u g)
    (hlc : IsUnit (algebraMap ℤ (Localization.Away c) N.leadingCoeff)) :
    Module.Finite (Localization.Away c) (Br A u g c) :=
  haveI : IsDomain (Localization.Away c) := isDomain_away hc
  finite_quotient_of_norm (Localization.Away c) (Aaway A c) c j u g N c' hfinA hN hlc

end finite_of_norm

end LevelBC
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_finite_levelRing.LevelBC"

end
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_finite_levelRing.LevelBC"

open Polynomial ModularCurve ModularCurve.HpoolLevelRing

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p)
    (v : Afin p)
    (hv : (v : ↥(modularFunctionFieldFull p)) = ⟨modularUnitSeries p, hmem⟩ ∨
      (v : ↥(modularFunctionFieldFull p)) =
        (p : ↥(modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : ↥(modularFunctionFieldFull p))⁻¹)
    (g : ℤ[X]) (hg : g.Monic) (hD : 1 ≤ g.natDegree) (h0 : g.coeff 0 ≠ 0)
    (c : ℤ) (hc : c ≠ 0) (hdiv : g.coeff 0 ∣ c) :
    Module.Finite (Localization.Away c) (levelRing p c v g) := by
  classical

  obtain ⟨N, ε, k, c', -, hlc, hc'A, hNc'⟩ :=
    ModularCurve.exists_int_poly_natDegree_aeval_jFull_eq_mul_aeval_modularUnitSeries p hmem
      (v : ↥(modularFunctionFieldFull p)) hv g hg hD h0

  have hN' : Polynomial.aeval
        (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) N =
      (⟨c', hc'A⟩ : Afin p) * Polynomial.aeval v g := by
    apply Subtype.ext
    have h1 := Polynomial.aeval_algHom_apply
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).val
      (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) N
    have h2 := Polynomial.aeval_algHom_apply
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).val v g
    simp only [Subalgebra.coe_val] at h1 h2
    rw [MulMemClass.coe_mul, ← h1, ← h2]
    exact hNc'

  have hlcU : IsUnit (algebraMap ℤ (Localization.Away c) N.leadingCoeff) := by
    rw [hlc, map_mul, map_pow]
    refine IsUnit.mul ((Units.isUnit ε).map _) (IsUnit.pow _ ?_)
    exact isUnit_of_dvd_unit (map_dvd (algebraMap ℤ (Localization.Away c)) hdiv) (IsLocalization.Away.algebraMap_isUnit c)

  have htjℚ : Transcendental ℚ (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) := by
    intro halg
    obtain ⟨q, hq, hev⟩ := halg
    refine ModularCurve.transcendental_jq ⟨q, hq, ?_⟩
    have h0' : (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ))
        ((Polynomial.aeval (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p))) q) = 0 := by
      rw [hev, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
        show (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)) (IgusaScheme.jFull p) = jq from
          IgusaScheme.coe_jFull p] at h0'
    rw [Polynomial.aeval_def]
    convert h0' using 2 <;> first | rfl | exact Subsingleton.elim _ _
  have htj : Transcendental ℤ (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) := fun h =>
    htjℚ ((IsFractionRing.isAlgebraic_iff ℤ ℚ ↥(modularFunctionFieldFull p)).mp h)
  have hFD := ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull p
  haveI := hFD
  have hsep : Algebra.IsSeparable
      ↥(IntermediateField.adjoin ℚ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)))
      ↥(modularFunctionFieldFull p) := inferInstance
  have hfin := (AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf ℤ ℚ
    ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) htj hFD hsep).1

  exact LevelBC.finite_of_norm (A := Afin p)
    (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) v g N
    ⟨c', hc'A⟩ c hc hfin hN' hlcU

end S_ModularCurve_HpoolLevelRing_finite_levelRing
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_finite_levelRing (solution)

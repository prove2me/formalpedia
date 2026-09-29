-- Prove2me | solution 1 for ModularCurve.kroneckerCongruence_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e9a0a443-492f-5fde-b312-c9090723450d

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_ModularCurve_LambdaModularPolynomialData_eval2_swap_eq_zero
import Theorems.Thm_ModularCurve_frobenius_identity_lambda
import Theorems.Thm_ModularCurve_transcendental_lambdaModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_kroneckerCongruence_lambda
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open Polynomial ModularCurve

noncomputable section

namespace LambdaKronSol

section Swap
variable (R : Type*) [CommRing R]

def inner : Polynomial R →+* Polynomial (Polynomial R) := Polynomial.mapRingHom (Polynomial.C : R →+* Polynomial R)

def swap : Polynomial (Polynomial R) →+* Polynomial (Polynomial R) :=
  Polynomial.eval₂RingHom (inner R) (Polynomial.C Polynomial.X)

variable {R}

@[scoped simp] theorem inner_C (r : R) : inner R (C r) = C (C r) := by simp [inner]
@[scoped simp] theorem inner_X : inner R X = X := by simp [inner]
@[scoped simp] theorem swap_C (p : Polynomial R) : swap R (C p) = inner R p := by simp [swap]
@[scoped simp] theorem swap_X : swap R X = C X := by simp [swap]
theorem swap_C_C (r : R) : swap R (C (C r)) = C (C r) := by rw [swap_C, inner_C]
theorem swap_C_X : swap R (C X) = X := by rw [swap_C, inner_X]

theorem swap_swap (P : Polynomial (Polynomial R)) : swap R (swap R P) = P := by
  have h : (swap R).comp (swap R) = RingHom.id _ := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · refine Polynomial.ringHom_ext' ?_ ?_
      · ext r; simp [swap_C_C]
      · simp [swap_C_X]
    · simp [swap_X, swap_C_X]
  exact congrArg (fun φ => φ P) h

theorem eval₂_swap {A : Type*} [CommRing A] (φ : R →+* A) (P : Polynomial (Polynomial R)) (x y : A) :
    (swap R P).eval₂ (Polynomial.eval₂RingHom φ x) y = P.eval₂ (Polynomial.eval₂RingHom φ y) x := by
  have h : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom φ x) y).comp (swap R)
      = Polynomial.eval₂RingHom (Polynomial.eval₂RingHom φ y) x := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · refine Polynomial.ringHom_ext' ?_ ?_
      · ext r; simp [swap_C_C]
      · simp [swap_C_X]
    · simp [swap_X]
  exact congrArg (fun ψ => ψ P) h

end Swap

variable (q : ℕ) [hq : Fact q.Prime]

local notation "𝔽" => ZMod q

scoped instance : NeZero q := ⟨hq.out.ne_zero⟩

theorem eval_int (data : LambdaModularPolynomialData q) :
    data.Ψ.eval₂ evalAtLambdaInt (qExpand ℤ q lambdaInt) = 0 := by
  apply laurentMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
  rw [map_zero, Polynomial.hom_eval₂, laurentMap_qExpand]
  exact data.eval_eq_zero

theorem laurentMap_comp_eval₂RingHom {S : Type*} [CommRing S] (f : ℤ →+* S) (z : LaurentSeries ℤ) :
    (laurentMap f).comp (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℤ)) z)
      = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries S)) (laurentMap f z) := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

theorem eval_int_swap (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) :
    data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℤ)) (qExpand ℤ q lambdaInt)) lambdaInt = 0 := by
  apply laurentMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
  rw [map_zero, Polynomial.hom_eval₂, laurentMap_comp_eval₂RingHom, laurentMap_qExpand]
  exact ModularCurve.LambdaModularPolynomialData.eval2_swap_eq_zero q hq2 data

abbrev ev (z : LaurentSeries 𝔽) : Polynomial 𝔽 →+* LaurentSeries 𝔽 :=
  Polynomial.eval₂RingHom (algebraMap 𝔽 (LaurentSeries 𝔽)) z

theorem red_lambdaInt : laurentMap (Int.castRingHom 𝔽) lambdaInt = lambdaModC 𝔽 := rfl

theorem red_qExpand_lambdaInt : laurentMap (Int.castRingHom 𝔽) (qExpand ℤ q lambdaInt) = lambdaModC 𝔽 ^ q := by
  rw [laurentMap_qExpand, red_lambdaInt]
  have h := ModularCurve.frobenius_identity_lambda (ZMod q) (ℓ := q)
  rw [lambdaNModC] at h
  exact h

theorem red_comp_evalAtLambdaInt :
    (laurentMap (Int.castRingHom 𝔽)).comp evalAtLambdaInt
      = (ev q (lambdaModC 𝔽)).comp (Polynomial.mapRingHom (Int.castRingHom 𝔽)) := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [evalAtLambdaInt_X, red_lambdaInt]

theorem red_comp_eval₂RingHom_qExpand :
    (laurentMap (Int.castRingHom 𝔽)).comp (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℤ)) (qExpand ℤ q lambdaInt))
      = (ev q (lambdaModC 𝔽 ^ q)).comp (Polynomial.mapRingHom (Int.castRingHom 𝔽)) := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [red_qExpand_lambdaInt]

theorem reduceModBivar_eq_map (P : Polynomial (Polynomial ℤ)) :
    reduceModBivar q P = P.map (Polynomial.mapRingHom (Int.castRingHom 𝔽)) := rfl

theorem redA (data : LambdaModularPolynomialData q) :
    (reduceModBivar q data.Ψ).eval₂ (ev q (lambdaModC 𝔽)) (lambdaModC 𝔽 ^ q) = 0 := by
  have h := congrArg (laurentMap (Int.castRingHom 𝔽)) (eval_int q data)
  rw [map_zero, Polynomial.hom_eval₂, red_comp_evalAtLambdaInt, red_qExpand_lambdaInt, ← Polynomial.eval₂_map] at h
  rw [reduceModBivar_eq_map]
  exact h

theorem redB (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) :
    (reduceModBivar q data.Ψ).eval₂ (ev q (lambdaModC 𝔽 ^ q)) (lambdaModC 𝔽) = 0 := by
  have h := congrArg (laurentMap (Int.castRingHom 𝔽)) (eval_int_swap q hq2 data)
  rw [map_zero, Polynomial.hom_eval₂, red_comp_eval₂RingHom_qExpand, red_lambdaInt, ← Polynomial.eval₂_map] at h
  rw [reduceModBivar_eq_map]
  exact h

theorem eq_zero_of_ev_eq_zero (G : Polynomial 𝔽) (hG : ev q (lambdaModC 𝔽) G = 0) : G = 0 :=
  (transcendental_iff.mp (ModularCurve.transcendental_lambdaModC (ZMod q))) G hG

theorem dvdA (data : LambdaModularPolynomialData q) :
    (X - C ((X : Polynomial 𝔽) ^ q)) ∣ reduceModBivar q data.Ψ := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
  apply eq_zero_of_ev_eq_zero q
  have h := Polynomial.hom_eval₂ (reduceModBivar q data.Ψ) (RingHom.id _) (ev q (lambdaModC 𝔽)) ((X : Polynomial 𝔽) ^ q)
  rw [RingHom.comp_id, map_pow] at h
  rw [Polynomial.eval, h]
  simpa using redA q data

theorem dvdB (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) :
    (C (X : Polynomial 𝔽) - X ^ q) ∣ reduceModBivar q data.Ψ := by
  have h1 : (X - C ((X : Polynomial 𝔽) ^ q)) ∣ swap 𝔽 (reduceModBivar q data.Ψ) := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
    apply eq_zero_of_ev_eq_zero q
    have h := Polynomial.hom_eval₂ (swap 𝔽 (reduceModBivar q data.Ψ)) (RingHom.id _) (ev q (lambdaModC 𝔽)) ((X : Polynomial 𝔽) ^ q)
    rw [RingHom.comp_id, map_pow] at h
    rw [Polynomial.eval, h]
    have h2 := eval₂_swap (algebraMap 𝔽 (LaurentSeries 𝔽)) (reduceModBivar q data.Ψ) (lambdaModC 𝔽) (lambdaModC 𝔽 ^ q)
    simp only [ev] at h2 ⊢
    rw [show (Polynomial.eval₂RingHom (algebraMap 𝔽 (LaurentSeries 𝔽)) (lambdaModC 𝔽)) X = lambdaModC 𝔽 from by simp]
    rw [h2]
    exact redB q hq2 data
  have h2 := map_dvd (swap 𝔽) h1
  rw [swap_swap, map_sub, swap_X, swap_C, map_pow, inner_X] at h2
  exact h2

theorem kron (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) :
    reduceModBivar q data.Ψ = (C X ^ q - X) * (C X - X ^ q) := by
  set a : Polynomial (Polynomial 𝔽) := X - C ((X : Polynomial 𝔽) ^ q) with ha_def
  set b : Polynomial (Polynomial 𝔽) := C (X : Polynomial 𝔽) - X ^ q with hb_def
  have ha : Prime a := Polynomial.prime_X_sub_C _
  have hq1 : 1 < q := hq.out.one_lt
  have hab : ¬ a ∣ b := by
    intro h
    rw [ha_def, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, hb_def] at h
    simp only [eval_sub, eval_C, eval_pow, eval_X] at h
    have hc := congrArg (fun p : Polynomial 𝔽 => p.coeff 1) h
    simp only [coeff_sub, coeff_X_one, coeff_zero, ← pow_mul] at hc
    rw [Polynomial.coeff_X_pow, if_neg (by nlinarith)] at hc
    simp at hc
  obtain ⟨H₁, hH₁⟩ := dvdB q hq2 data
  have haH : a ∣ H₁ := by
    rcases ha.dvd_or_dvd (show a ∣ b * H₁ from hH₁ ▸ dvdA q data) with h | h
    · exact absurd h hab
    · exact h
  obtain ⟨H₂, hH₂⟩ := haH
  set M : Polynomial (Polynomial 𝔽) := (C X ^ q - X) * (C X - X ^ q) with hM_def
  have hMdvd : M ∣ reduceModBivar q data.Ψ := by
    refine ⟨-H₂, ?_⟩
    rw [hH₁, hH₂]
    simp only [hM_def, ha_def, hb_def, map_pow]
    ring

  have hΨm : (reduceModBivar q data.Ψ).Monic := by
    rw [reduceModBivar_eq_map]; exact data.monic.map _
  have hΨd : (reduceModBivar q data.Ψ).natDegree = q + 1 := by
    rw [reduceModBivar_eq_map, data.monic.natDegree_map, data.natDegree_eq]
  have hM' : M = (X - C ((X : Polynomial 𝔽) ^ q)) * (X ^ q - C (X : Polynomial 𝔽)) := by
    rw [hM_def, map_pow]; ring
  have hMm : M.Monic := by
    rw [hM']
    exact (monic_X_sub_C _).mul (monic_X_pow_sub_C _ hq.out.ne_zero)
  have hMd : M.natDegree = q + 1 := by
    rw [hM', (monic_X_sub_C _).natDegree_mul (monic_X_pow_sub_C _ hq.out.ne_zero), natDegree_X_sub_C,
      natDegree_X_pow_sub_C]
    ring
  have := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hMm hΨm hMdvd (by rw [hΨd, hMd])
  rw [this]

end LambdaKronSol
p2m_reactivate "P2MW.S_ModularCurve_kroneckerCongruence_lambda.LambdaKronSol"

end
p2m_reactivate "P2MW.S_ModularCurve_kroneckerCongruence_lambda.LambdaKronSol"

theorem solution (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) :
    reduceModBivar q data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) :=
  LambdaKronSol.kron q hq2 data

end S_ModularCurve_kroneckerCongruence_lambda
end P2MW
export P2MW.S_ModularCurve_kroneckerCongruence_lambda (solution)

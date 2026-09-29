-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ece2eb01-7ce6-55da-8ce9-5a380fc8e0e4

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_ModularCurve_exists_lambdaKroneckerCongruence
import Theorems.Thm_ModularCurve_minpoly_lambdaNModC_eq
import Theorems.Thm_ModularCurve_transcendental_lambdaModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized Polynomial

theorem solution
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (l : k) (hl2 : l ^ (q ^ 2) = l)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (s : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (hs : lambdaEval q (coeffSubring A K) s = 0) :
    NodeLocalized.pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q) s = 0 := by
  classical
  have hqP : q.Prime := Fact.out
  obtain ⟨data, hKr⟩ := ModularCurve.exists_lambdaKroneckerCongruence q hq2
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* Polynomial (Polynomial ↥(coeffSubring A K)),
      ψ = MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C) ![Polynomial.C Polynomial.X, Polynomial.X] := ⟨_, rfl⟩
  obtain ⟨EV, hEVd⟩ : ∃ EV : Polynomial (Polynomial ↥(coeffSubring A K)) →+* LaurentSeries (AlgebraicClosure ℚ),
      EV = Polynomial.eval₂RingHom
        (Polynomial.eval₂RingHom (CharPReduction.constSeries (coeffSubring A K)) (lambdaModC (AlgebraicClosure ℚ)))
        (lambdaNModC (AlgebraicClosure ℚ) q) := ⟨_, rfl⟩
  obtain ⟨PT, hPTd⟩ : ∃ PT : Polynomial (Polynomial ↥(coeffSubring A K)) →+* k,
      PT = Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (redRestrict red K) l) (l ^ q) := ⟨_, rfl⟩
  have hEV : (lambdaEval q (coeffSubring A K) : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* _) = EV.comp ψ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [lambdaEval, hψ, hEVd]
    · fin_cases i <;> simp [lambdaEval, hψ, hEVd]
  have hPT : (NodeLocalized.pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q) : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* k) = PT.comp ψ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [NodeLocalized.pointEval, hψ, hPTd]
    · fin_cases i <;> simp [NodeLocalized.pointEval, hψ, hPTd]

  let ΨR : Polynomial (Polynomial ↥(coeffSubring A K)) := data.Ψ.map (Polynomial.mapRingHom (Int.castRingHom ↥(coeffSubring A K)))
  have hΨmonic : ΨR.Monic := data.monic.map _

  let F := IntermediateField.adjoin (AlgebraicClosure ℚ) ({lambdaModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))
  let μF : ↥F := ⟨lambdaModC (AlgebraicClosure ℚ), IntermediateField.mem_adjoin_simple_self _ _⟩
  let ι : ↥(coeffSubring A K) →+* AlgebraicClosure ℚ := (coeffSubring A K).subtype
  obtain ⟨θ₀, hθ₀d⟩ : ∃ θ₀ : Polynomial ↥(coeffSubring A K) →+* ↥F,
      θ₀ = Polynomial.eval₂RingHom ((algebraMap (AlgebraicClosure ℚ) ↥F).comp ι) μF := ⟨_, rfl⟩
  obtain ⟨θ, hθd⟩ : ∃ θ : Polynomial (Polynomial ↥(coeffSubring A K)) →+* Polynomial ↥F, θ = Polynomial.mapRingHom θ₀ := ⟨_, rfl⟩
  have hθ₀L : (algebraMap ↥F (LaurentSeries (AlgebraicClosure ℚ))).comp θ₀
      = Polynomial.eval₂RingHom (CharPReduction.constSeries (coeffSubring A K)) (lambdaModC (AlgebraicClosure ℚ)) := by
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · simp [hθ₀d, ι, CharPReduction.constSeries]
    · simp [hθ₀d, μF]
  have hEVθ : EV = (Polynomial.eval₂RingHom (algebraMap ↥F (LaurentSeries (AlgebraicClosure ℚ)))
      (lambdaNModC (AlgebraicClosure ℚ) q)).comp θ := by
    refine Polynomial.ringHom_ext (fun p => ?_) ?_
    · rw [hEVd, hθd]
      simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C]
      exact (congrArg (fun g : Polynomial ↥(coeffSubring A K) →+* _ => g p) hθ₀L).symm
    · rw [hEVd, hθd]; simp

  have hθ₀ : Function.Injective θ₀ := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have h1 : (θ₀ p : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by rw [hp]; rfl
    have h2 : (θ₀ p : LaurentSeries (AlgebraicClosure ℚ))
        = Polynomial.aeval (lambdaModC (AlgebraicClosure ℚ)) (p.map ι) := by
      have := congrArg (fun g : Polynomial ↥(coeffSubring A K) →+* _ => g p) hθ₀L
      simp only [RingHom.coe_comp, Function.comp_apply] at this
      rw [show ((θ₀ p : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) = algebraMap ↥F _ (θ₀ p) from rfl, this,
        Polynomial.coe_eval₂RingHom, Polynomial.aeval_def, Polynomial.eval₂_map]
      rfl
    rw [h2] at h1
    have h3 : p.map ι = 0 :=
      (transcendental_iff_injective.mp (ModularCurve.transcendental_lambdaModC (AlgebraicClosure ℚ)))
        (by rw [h1, map_zero])
    exact (Polynomial.map_injective ι Subtype.val_injective) (by rw [h3, Polynomial.map_zero])
  have hθ : Function.Injective θ := by rw [hθd]; exact Polynomial.map_injective θ₀ hθ₀

  have hθΨ : θ ΨR = minpoly ↥F (lambdaNModC (AlgebraicClosure ℚ) q) := by
    rw [ModularCurve.minpoly_lambdaNModC_eq (AlgebraicClosure ℚ) q hq2 data]
    simp only [hθd, ΨR, Polynomial.coe_mapRingHom, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [hθ₀d, μF]

  set p := ψ s with hp
  have hEVp : EV p = 0 := by
    have := congrArg (fun g : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* _ => g s) hEV
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    rw [← this]; exact hs
  have hEVΨ : EV ΨR = 0 := by
    rw [hEVθ, RingHom.comp_apply, hθΨ, Polynomial.coe_eval₂RingHom, ← Polynomial.aeval_def]
    exact minpoly.aeval ↥F _
  set r := p %ₘ ΨR with hr
  have hEVr : EV r = 0 := by
    have hdiv := Polynomial.modByMonic_add_div p ΨR
    have := congrArg EV hdiv
    rw [map_add, map_mul, hEVΨ, zero_mul, add_zero, hEVp] at this
    exact this
  have hr0 : r = 0 := by
    apply hθ
    rw [map_zero]
    by_contra hne
    have haeval : Polynomial.aeval (lambdaNModC (AlgebraicClosure ℚ) q) (θ r) = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.coe_eval₂RingHom, ← RingHom.comp_apply, ← hEVθ]
      exact hEVr
    have hle := minpoly.degree_le_of_ne_zero ↥F (lambdaNModC (AlgebraicClosure ℚ) q) hne haeval
    have hlt : (θ r).degree < (minpoly ↥F (lambdaNModC (AlgebraicClosure ℚ) q)).degree := by
      rw [← hθΨ]
      calc (θ r).degree ≤ r.degree := by rw [hθd]; exact Polynomial.degree_map_le
        _ < ΨR.degree := Polynomial.degree_modByMonic_lt p hΨmonic
        _ = (θ ΨR).degree := by rw [hθd]; exact (hΨmonic.degree_map θ₀).symm
    exact absurd hle (not_le.mpr hlt)
  have hfac : p = ΨR * (p /ₘ ΨR) := by
    have hdiv := Polynomial.modByMonic_add_div p ΨR
    rw [← hr, hr0, zero_add] at hdiv
    exact hdiv.symm

  have hPTΨ : PT ΨR = 0 := by
    obtain ⟨ρ, hρd⟩ : ∃ ρ : Polynomial (Polynomial (ZMod q)) →+* k,
        ρ = Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl q) k) l) (l ^ q) := ⟨_, rfl⟩
    have hcomp : PT.comp (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ↥(coeffSubring A K)))) =
        ρ.comp (reduceModBivar q) := by
      refine Polynomial.ringHom_ext' ?_ ?_
      · refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
        simp [hPTd, hρd, reduceModBivar]
      · simp [hPTd, hρd, reduceModBivar]
    have h1 : PT ΨR = ρ (reduceModBivar q data.Ψ) := by
      have := congrArg (fun g => g data.Ψ) hcomp
      simpa using this
    rw [h1, hKr, map_mul]
    have hzero : ρ (Polynomial.C Polynomial.X ^ q - Polynomial.X) = 0 := by
      rw [map_sub, map_pow, hρd]
      simp
    rw [hzero, zero_mul]

  have := congrArg (fun g : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* k => g s) hPT
  simp only [RingHom.coe_comp, Function.comp_apply] at this
  rw [this, ← hp, hfac, map_mul, hPTΨ, zero_mul]

end S_ModularCurve_LambdaNodeLocalized_pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two (solution)

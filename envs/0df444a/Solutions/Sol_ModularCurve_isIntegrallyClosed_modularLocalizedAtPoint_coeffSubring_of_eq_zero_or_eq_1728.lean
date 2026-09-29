-- Prove2me | solution 1 for ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/3df993b9-e6dd-5f60-a059-f1861f30746a

import Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
import Theorems.Thm_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_isUnit
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm"
p2m_attr_erase "simp" "Localization.AtPrime.quotientPowEquiv_mk ModularCurve.NodeLocalized.coe_modularEvalAt AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"
set_option autoImplicit false

noncomputable section

p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728.ModularCurve ModularCurve.NodeLocalized"

namespace ModularCurve
p2m_export "ModularCurve" "exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728 ssJSet jWidth jWidth_pos NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring"
namespace NodeNormality
p2m_open "ModularCurve"

private theorem redRestrict_natCast (q : ℕ) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    redRestrict red K ((q : ℕ) : ↥(coeffSubring A K)) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

private theorem natCast_ne_zero (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : ((q : ℕ) : ↥(coeffSubring A K)) ≠ 0 := by
  intro h
  have h' := congrArg (fun z : ↥(coeffSubring A K) => (z : AlgebraicClosure ℚ)) h
  simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero] at h'
  exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) h'

private theorem isDiscreteValuationRing_coeffSubring (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [CharP k q] [FiniteDimensional ℚ K] :
    IsDiscreteValuationRing ↥(coeffSubring A K) := by
  rcases coeffSubring_eq_or_isDiscreteValuationRing A K with h | h
  · exfalso
    have hqK : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ K.toSubalgebra.toSubring := by
      rw [Subalgebra.mem_toSubring, IntermediateField.mem_toSubalgebra]
      exact inv_mem (natCast_mem K q)
    have hmem : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
      rw [h]
      exact hqK
    have h1 : ((q : ℕ) : ↥(coeffSubring A K)) * (⟨_, hmem⟩ : ↥(coeffSubring A K)) = 1 := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, SubringClass.coe_natCast, OneMemClass.coe_one]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
    have h2 := congrArg (redRestrict red K) h1
    rw [map_mul, map_one, redRestrict_natCast q red K, zero_mul] at h2
    exact zero_ne_one h2
  · exact h

private theorem ker_redRestrict_eq (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [CharP k q] [FiniteDimensional ℚ K] :
    RingHom.ker (redRestrict red K) = @maximalIdeal ↥(coeffSubring A K) _
      (isDiscreteValuationRing_coeffSubring q red K).toIsLocalRing := by
  haveI := isDiscreteValuationRing_coeffSubring q red K
  have hne : RingHom.ker (redRestrict red K) ≠ ⊥ := by
    intro hbot
    have hq : ((q : ℕ) : ↥(coeffSubring A K)) ∈ RingHom.ker (redRestrict red K) := by
      rw [RingHom.mem_ker]
      exact redRestrict_natCast q red K
    rw [hbot, Ideal.mem_bot] at hq
    exact natCast_ne_zero q K hq
  exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) hne)

private theorem exists_uniformizer (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [CharP k q] [FiniteDimensional ℚ K] :
    ∃ ϖ : ↥(coeffSubring A K), Irreducible ϖ ∧ ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d := by
  haveI := isDiscreteValuationRing_coeffSubring q red K
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)
  have hspan : maximalIdeal ↥(coeffSubring A K) = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hirr
  refine ⟨ϖ, hirr, fun c => ?_⟩
  rw [← RingHom.mem_ker, ker_redRestrict_eq q red K, hspan, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d, mul_comm _ _⟩
  · rintro ⟨d, rfl⟩
    exact ⟨d, mul_comm _ _⟩

section Residue

private def constHom (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (a : k) : ↥(coeffSubring A K) →+* ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
  RingHom.codRestrict ((modularEval (1 * q) (coeffSubring A K)).comp MvPolynomial.C) _
    (fun c => modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)
      (MvPolynomial.C c))

private def polyHom (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (a : k) : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
  RingHom.codRestrict (modularEval (1 * q) (coeffSubring A K)) _
    (fun p => modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) p)

private theorem polyHom_C (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (a : k) (c : ↥(coeffSubring A K)) :
    polyHom q red K a (MvPolynomial.C c) = constHom q red K a c := rfl

private theorem pointEval_eq (q : ℕ) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (a : k) (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a) :
    pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q)
      = (redRestrict red K).comp (MvPolynomial.eval ![x, x ^ q]) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
  · show MvPolynomial.eval₂Hom (redRestrict red K) ![a, a ^ q] (MvPolynomial.C c) = _
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.eval_C]
  · show MvPolynomial.eval₂Hom (redRestrict red K) ![a, a ^ q] (MvPolynomial.X i) = _
    rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, MvPolynomial.eval_X]
    fin_cases i
    · simp [hx]
    · simp [hx, map_pow]

private theorem polyHom_sub_constHom_eval_mem (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (a : k) (x : ↥(coeffSubring A K)) (I : Ideal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (h0 : polyHom q red K a (MvPolynomial.X 0) - constHom q red K a x ∈ I)
    (h1 : polyHom q red K a (MvPolynomial.X 1) - constHom q red K a (x ^ q) ∈ I)
    (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    polyHom q red K a p - constHom q red K a (MvPolynomial.eval ![x, x ^ q] p) ∈ I := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.eval_C, polyHom_C q red K a, sub_self]
    exact I.zero_mem
  | add p r hp hr =>
    have h : polyHom q red K a (p + r) - constHom q red K a (MvPolynomial.eval ![x, x ^ q] (p + r))
        = (polyHom q red K a p - constHom q red K a (MvPolynomial.eval ![x, x ^ q] p))
          + (polyHom q red K a r - constHom q red K a (MvPolynomial.eval ![x, x ^ q] r)) := by
      rw [map_add, map_add, map_add]
      ring
    rw [h]
    exact I.add_mem hp hr
  | mul_X p i hp =>
    have hXi : polyHom q red K a (MvPolynomial.X i) - constHom q red K a (![x, x ^ q] i) ∈ I := by
      fin_cases i
      · exact h0
      · exact h1
    have h : polyHom q red K a (p * MvPolynomial.X i)
          - constHom q red K a (MvPolynomial.eval ![x, x ^ q] (p * MvPolynomial.X i))
        = polyHom q red K a p * (polyHom q red K a (MvPolynomial.X i) - constHom q red K a (![x, x ^ q] i))
          + (polyHom q red K a p - constHom q red K a (MvPolynomial.eval ![x, x ^ q] p))
            * constHom q red K a (![x, x ^ q] i) := by
      rw [map_mul, map_mul, MvPolynomial.eval_X, map_mul]
      ring
    rw [h]
    exact I.add_mem (I.mul_mem_left _ hXi) (I.mul_mem_right _ hp)

private theorem exists_sub_constHom_mem (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [CharP k q] [FiniteDimensional ℚ K]
    (a : k) (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a) (I : Ideal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (h0 : polyHom q red K a (MvPolynomial.X 0) - constHom q red K a x ∈ I)
    (h1 : polyHom q red K a (MvPolynomial.X 1) - constHom q red K a (x ^ q) ∈ I)
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    ∃ c : ↥(coeffSubring A K), f - constHom q red K a c ∈ I := by
  obtain ⟨r, s, hs, hfs⟩ := f.2

  have hs0 : redRestrict red K (MvPolynomial.eval ![x, x ^ q] s) ≠ 0 := by
    have h := hs
    rw [pointEval_eq q red K a x hx, RingHom.comp_apply] at h
    exact h
  haveI := isDiscreteValuationRing_coeffSubring q red K
  have hsu : IsUnit (MvPolynomial.eval ![x, x ^ q] s) := by
    refine IsLocalRing.notMem_maximalIdeal.mp fun hm => hs0 ?_
    rw [← ker_redRestrict_eq q red K, RingHom.mem_ker] at hm
    exact hm

  have hfs' : f * polyHom q red K a s = polyHom q red K a r := Subtype.ext hfs
  have hr := polyHom_sub_constHom_eval_mem q red K a x I h0 h1 r
  have hs' := polyHom_sub_constHom_eval_mem q red K a x I h0 h1 s
  have key : f * constHom q red K a (MvPolynomial.eval ![x, x ^ q] s)
      - constHom q red K a (MvPolynomial.eval ![x, x ^ q] r) ∈ I := by
    have h : f * constHom q red K a (MvPolynomial.eval ![x, x ^ q] s) - constHom q red K a (MvPolynomial.eval ![x, x ^ q] r)
        = (polyHom q red K a r - constHom q red K a (MvPolynomial.eval ![x, x ^ q] r))
          - f * (polyHom q red K a s - constHom q red K a (MvPolynomial.eval ![x, x ^ q] s)) := by
      rw [← hfs']
      ring
    rw [h]
    exact I.sub_mem hr (I.mul_mem_left _ hs')
  obtain ⟨u, hu⟩ := hsu
  refine ⟨MvPolynomial.eval ![x, x ^ q] r * ↑u⁻¹, ?_⟩
  have hunit : IsUnit (constHom q red K a (MvPolynomial.eval ![x, x ^ q] s)) := by
    rw [← hu]
    exact (Units.isUnit u).map _
  rw [← Ideal.mul_unit_mem_iff_mem I hunit]
  have hc : MvPolynomial.eval ![x, x ^ q] r * ↑u⁻¹ * MvPolynomial.eval ![x, x ^ q] s
      = MvPolynomial.eval ![x, x ^ q] r := by
    rw [← hu, mul_assoc, Units.inv_mul, mul_one]
  rw [sub_mul, ← map_mul, hc]
  exact key

end Residue

end ModularCurve.NodeNormality

end

p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728.ModularCurve"
open ModularCurve.NodeLocalized

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (hq : 5 ≤ q) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hx : ∃ x : ↥(coeffSubring A K), redRestrict red K x = a) :
    IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
  have _ := h01728
  obtain ⟨x, hx⟩ := hx
  obtain ⟨ϖ, hirr, hϖ⟩ := ModularCurve.NodeNormality.exists_uniformizer q red K
  obtain ⟨eK, ε, heK1, _, _, G', H', w, hw, hGH, hmax, hpr1, hpr2, hnm1, hnm2, _, _⟩ :=
    ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728 red a ha ha2 hq
      h01728 K x hx ϖ hϖ
  obtain ⟨hN, hL, -, hmaxB⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx ϖ hϖ
  haveI : IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := hN
  haveI : IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := hL
  haveI : IsDiscreteValuationRing ↥(coeffSubring A K) := ModularCurve.NodeNormality.isDiscreteValuationRing_coeffSubring q red K
  letI : Algebra ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := (ModularCurve.NodeNormality.constHom q red K a).toAlgebra
  have hmap : ∀ c : ↥(coeffSubring A K), algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) c = ModularCurve.NodeNormality.constHom q red K a c := fun _ => rfl
  have hmapϖ : algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ
      = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) := rfl

  have hm0 : ModularCurve.NodeNormality.polyHom q red K a (MvPolynomial.X 0) - ModularCurve.NodeNormality.constHom q red K a x
      ∈ maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
    have h : ModularCurve.NodeNormality.polyHom q red K a (MvPolynomial.X 0)
          - ModularCurve.NodeNormality.constHom q red K a x
        = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C x),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :=
      Subtype.ext (by
        change _ = modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C x)
        rw [map_sub]
        rfl)
    rw [h, hmaxB]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hm1 : ModularCurve.NodeNormality.polyHom q red K a (MvPolynomial.X 1)
        - ModularCurve.NodeNormality.constHom q red K a (x ^ q)
      ∈ maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
    have h : ModularCurve.NodeNormality.polyHom q red K a (MvPolynomial.X 1)
          - ModularCurve.NodeNormality.constHom q red K a (x ^ q)
        = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :=
      Subtype.ext (by
        change _ = modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))
        rw [map_sub]
        rfl)
    rw [h, hmaxB]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

  have hres : Function.Surjective ((IsLocalRing.residue ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))).comp (algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) := by
    intro z
    obtain ⟨f, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨c, hc⟩ :=
      ModularCurve.NodeNormality.exists_sub_constHom_mem q red K a x hx (maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) hm0 hm1 f
    refine ⟨c, ?_⟩
    rw [RingHom.comp_apply, hmap, eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hc

  have he : 1 ≤ jWidth a * eK := Nat.mul_pos (jWidth_pos a) heK1
  have hGH' : G' * H' = algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ ^ (jWidth a * eK) * w := by
    rw [hmapϖ]
    exact hGH
  have hmax' : maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = Ideal.span {algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ, G', H'} := by
    rw [hmapϖ]
    exact hmax
  have hpr1' : (Ideal.span {algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ, G'}).IsPrime := by
    rw [hmapϖ]
    exact hpr1
  have hpr2' : (Ideal.span {algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ, H'}).IsPrime := by
    rw [hmapϖ]
    exact hpr2
  have hnm1' : H' ∉ Ideal.span {algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ, G'} := by
    rw [hmapϖ]
    exact hnm1
  have hnm2' : G' ∉ Ideal.span {algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ, H'} := by
    rw [hmapϖ]
    exact hnm2
  exact IsLocalRing.isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_isUnit
    ϖ hirr hres G' H' w hw (jWidth a * eK) he hGH' hmax' hpr1' hpr2' hnm1' hnm2'

#print axioms solution

end S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
end P2MW
export P2MW.S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728 (solution)

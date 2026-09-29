-- Prove2me | solution 1 for ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/081b7b9a-aa44-5faf-ab1f-b92f4355a651

import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularLocus
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_ClassicalModularPolynomials
import Theorems.Thm_ModularCurve_phiTwo_eval2_evalAtJ_jqN_two_eq_zero
import Theorems.Thm_ModularCurve_phiTwo_eq_mul_add_pow_twelve_mul
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_two
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"
set_option autoImplicit false

p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_two.ModularCurve"
open ModularCurve.NodeLocalized

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC jqN evalAtJ evalAtJ_X autWeight laurentMap laurentMap_qExpand phiTwo phiTwo_eval2_evalAtJ_jqN_two_eq_zero phiTwo_eq_mul_add_pow_twelve_mul"
p2m_open "ModularCurve"

private noncomputable def evalJBar : Polynomial ℤ →+* LaurentSeries (AlgebraicClosure ℚ) :=
  Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) (jqModC (AlgebraicClosure ℚ))

private theorem laurentMap_comp_evalAtJ :
    (laurentMap (algebraMap ℚ (AlgebraicClosure ℚ))).comp evalAtJ = evalJBar := by
  apply Polynomial.ringHom_ext
  · intro n
    simp only [evalAtJ, evalJBar, eq_intCast, map_intCast]
  · simp only [RingHom.comp_apply, evalAtJ_X, evalJBar, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

private theorem laurentMap_jqN_two :
    laurentMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqN 2) = jqNModC (AlgebraicClosure ℚ) 2 := by
  unfold jqN jqNModC
  rw [laurentMap_qExpand]
  congr 1
  exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

private theorem phiTwo_eval₂_bar : phiTwo.eval₂ evalJBar (jqNModC (AlgebraicClosure ℚ) 2) = 0 := by
  have h := congrArg (laurentMap (algebraMap ℚ (AlgebraicClosure ℚ))) phiTwo_eval2_evalAtJ_jqN_two_eq_zero
  rwa [map_zero, Polynomial.hom_eval₂, laurentMap_comp_evalAtJ, laurentMap_jqN_two] at h

private theorem branchFactor_mul_branchFactor_laurent :
    (jqModC (AlgebraicClosure ℚ) ^ 2 + 2608 * jqModC (AlgebraicClosure ℚ) + 768 - jqNModC (AlgebraicClosure ℚ) 2)
        * (jqModC (AlgebraicClosure ℚ) - jqNModC (AlgebraicClosure ℚ) 2 ^ 2
            + 1488 * jqNModC (AlgebraicClosure ℚ) 2 + 3328)
      = -(2 ^ 12 * ((-38443359999 + 2133623 * jqModC (AlgebraicClosure ℚ) - 41 * jqModC (AlgebraicClosure ℚ) ^ 2)
          + (2135464 + 9007 * jqModC (AlgebraicClosure ℚ)) * jqNModC (AlgebraicClosure ℚ) 2
          + (-39 + jqModC (AlgebraicClosure ℚ)) * jqNModC (AlgebraicClosure ℚ) 2 ^ 2)) := by
  have h := phiTwo_eval₂_bar
  rw [phiTwo_eq_mul_add_pow_twelve_mul] at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_neg, Polynomial.eval₂_ofNat, Polynomial.eval₂_X, Polynomial.eval₂_C, evalJBar,
    Polynomial.coe_eval₂RingHom] at h
  linear_combination h

section NodeRing

private theorem modularEval_X_zero {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0) = jqModC (AlgebraicClosure ℚ) := by
  simp [modularEval]

private theorem modularEval_X_one {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1) = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
  simp [modularEval]

private theorem modularEval_branchFactor_mul_branchFactor_two {q : ℕ} [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hq2 : q = 2) :
    modularEval (1 * q) (coeffSubring A K)
        (MvPolynomial.X 0 ^ 2 + 2608 * MvPolynomial.X 0 + 768 - MvPolynomial.X 1)
      * modularEval (1 * q) (coeffSubring A K)
        (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2 + 1488 * MvPolynomial.X 1 + 3328)
      = -((2 : LaurentSeries (AlgebraicClosure ℚ)) ^ 12
          * modularEval (1 * q) (coeffSubring A K)
            ((-38443359999 + 2133623 * MvPolynomial.X 0 - 41 * MvPolynomial.X 0 ^ 2)
              + (2135464 + 9007 * MvPolynomial.X 0) * MvPolynomial.X 1
              + (-39 + MvPolynomial.X 0) * MvPolynomial.X 1 ^ 2)) := by
  subst hq2
  have h12 : jqNModC (AlgebraicClosure ℚ) (1 * 2) = jqNModC (AlgebraicClosure ℚ) 2 := rfl
  simp only [map_add, map_mul, map_sub, map_pow, map_neg, map_ofNat, modularEval_X_zero, modularEval_X_one, h12]
  exact branchFactor_mul_branchFactor_laurent

private theorem pointEval_cofactor_two_ne_zero {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hq2 : q = 2)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    pointEval (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)
        ((-38443359999 + 2133623 * MvPolynomial.X 0 - 41 * MvPolynomial.X 0 ^ 2)
          + (2135464 + 9007 * MvPolynomial.X 0) * MvPolynomial.X 1
          + (-39 + MvPolynomial.X 0) * MvPolynomial.X 1 ^ 2) ≠ 0 := by
  subst hq2
  simp only [pointEval, map_add, map_mul, map_sub, map_pow, map_neg, map_ofNat, MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  have h' : ((38443359999 : ℕ) : k) = 0 := by
    have h0 : (0 : k) ^ 2 = 0 := by simp
    rw [h0] at h
    norm_num at h
    exact_mod_cast h
  rw [CharP.cast_eq_zero_iff k 2] at h'
  omega

end NodeRing

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC jqN evalAtJ evalAtJ_X autWeight laurentMap laurentMap_qExpand phiTwo phiTwo_eval2_evalAtJ_jqN_two_eq_zero phiTwo_eq_mul_add_pow_twelve_mul"
p2m_open "ModularCurve"
namespace PhiTwoNode

private theorem crossing_span_pair_eq {R : Type*} [CommRing R] {ϖ G g : R}
    (hG : G ∈ Ideal.span {ϖ, g}) (hg : g ∈ Ideal.span {ϖ, G}) :
    Ideal.span {ϖ, G} = Ideal.span {ϖ, g} := by
  apply le_antisymm
  · exact Ideal.span_le.mpr (Set.insert_subset_iff.mpr
      ⟨Ideal.subset_span (Set.mem_insert _ _), Set.singleton_subset_iff.mpr hG⟩)
  · exact Ideal.span_le.mpr (Set.insert_subset_iff.mpr
      ⟨Ideal.subset_span (Set.mem_insert _ _), Set.singleton_subset_iff.mpr hg⟩)

private theorem crossing_span_triple_le {R : Type*} [CommRing R] {x y z : R} {I : Ideal R}
    (hx : x ∈ I) (hy : y ∈ I) (hz : z ∈ I) : Ideal.span {x, y, z} ≤ I :=
  Ideal.span_le.mpr (Set.insert_subset_iff.mpr ⟨hx, Set.insert_subset_iff.mpr
    ⟨hy, Set.singleton_subset_iff.mpr hz⟩⟩)

private theorem crossing_ideals_of_branches {R : Type*} [CommRing R] [IsLocalRing R]
    (ϖ j j₂ g h G H a b : R) (hg : g = j₂ - j ^ 2) (hh : h = j - j₂ ^ 2)
    (hG : G = -g + ϖ * a) (hH : H = h + ϖ * b)
    (hpg : (Ideal.span {ϖ, g}).IsPrime) (hph : (Ideal.span {ϖ, h}).IsPrime)
    (hhg : h ∉ Ideal.span {ϖ, g}) (hgh : g ∉ Ideal.span {ϖ, h})
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {ϖ, j, j₂}) :
    IsLocalRing.maximalIdeal R = Ideal.span {ϖ, G, H} ∧
      (Ideal.span {ϖ, G}).IsPrime ∧ (Ideal.span {ϖ, H}).IsPrime ∧
      H ∉ Ideal.span {ϖ, G} ∧ G ∉ Ideal.span {ϖ, H} ∧
      Ideal.span {ϖ, G} = Ideal.span {ϖ, g} ∧ Ideal.span {ϖ, H} = Ideal.span {ϖ, h} := by
  have hg' : g = -G + ϖ * a := by rw [hG]; ring
  have hh' : h = H - ϖ * b := by rw [hH]; ring
  have eG : Ideal.span {ϖ, G} = Ideal.span {ϖ, g} :=
    crossing_span_pair_eq (Ideal.mem_span_pair.mpr ⟨a, -1, by rw [hG]; ring⟩)
      (Ideal.mem_span_pair.mpr ⟨a, -1, by rw [hg']; ring⟩)
  have eH : Ideal.span {ϖ, H} = Ideal.span {ϖ, h} :=
    crossing_span_pair_eq (Ideal.mem_span_pair.mpr ⟨b, 1, by rw [hH]; ring⟩)
      (Ideal.mem_span_pair.mpr ⟨-b, 1, by rw [hh']; ring⟩)
  have hHg : H ∉ Ideal.span {ϖ, g} := fun hmem => hhg (by
    rw [hh']
    exact (Ideal.span {ϖ, g}).sub_mem hmem
      ((Ideal.span {ϖ, g}).mul_mem_right _ (Ideal.subset_span (Set.mem_insert _ _))))
  have hGh : G ∉ Ideal.span {ϖ, h} := fun hmem => hgh (by
    rw [hg']
    exact (Ideal.span {ϖ, h}).add_mem ((Ideal.span {ϖ, h}).neg_mem hmem)
      ((Ideal.span {ϖ, h}).mul_mem_right _ (Ideal.subset_span (Set.mem_insert _ _))))
  refine ⟨?_, eG ▸ hpg, eH ▸ hph, eG ▸ hHg, eH ▸ hGh, eG, eH⟩

  set I := Ideal.span {ϖ, g, h} with hI
  have hϖI : ϖ ∈ I := Ideal.subset_span (by simp)
  have hgI : g ∈ I := Ideal.subset_span (by simp)
  have hhI : h ∈ I := Ideal.subset_span (by simp)
  set J := Ideal.span {ϖ, G, H} with hJ
  have hϖJ : ϖ ∈ J := Ideal.subset_span (by simp)
  have hGJ : G ∈ J := Ideal.subset_span (by simp)
  have hHJ : H ∈ J := Ideal.subset_span (by simp)
  have hIJ : I = J := by
    apply le_antisymm
    · refine crossing_span_triple_le hϖJ ?_ ?_
      · rw [hg']; exact J.add_mem (J.neg_mem hGJ) (J.mul_mem_right _ hϖJ)
      · rw [hh']; exact J.sub_mem hHJ (J.mul_mem_right _ hϖJ)
    · refine crossing_span_triple_le hϖI ?_ ?_
      · rw [hG]; exact I.add_mem (I.neg_mem hgI) (I.mul_mem_right _ hϖI)
      · rw [hH]; exact I.add_mem hhI (I.mul_mem_right _ hϖI)

  have hjm : j ∈ IsLocalRing.maximalIdeal R := by rw [hm]; exact Ideal.subset_span (by simp)
  have hu : IsUnit (1 - j ^ 3) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp
        ((IsLocalRing.maximalIdeal R).pow_mem_of_mem hjm 3 (by norm_num)))
  have hjI : j ∈ I := by
    have key : (1 - j ^ 3) * j ∈ I := by
      have e : (1 - j ^ 3) * j = h + g * (j₂ + j ^ 2) := by rw [hg, hh]; ring
      rw [e]; exact I.add_mem hhI (I.mul_mem_right _ hgI)
    exact (Ideal.unit_mul_mem_iff_mem I hu).mp key
  have hj₂I : j₂ ∈ I := by
    have e : j₂ = g + j ^ 2 := by rw [hg]; ring
    rw [e]; exact I.add_mem hgI (I.pow_mem_of_mem hjI 2 (by norm_num))
  rw [hm, ← hIJ]
  apply le_antisymm
  · exact crossing_span_triple_le hϖI hjI hj₂I
  · refine crossing_span_triple_le (Ideal.subset_span (by simp)) ?_ ?_
    · rw [hg]
      exact (Ideal.span {ϖ, j, j₂}).sub_mem (Ideal.subset_span (by simp))
        ((Ideal.span {ϖ, j, j₂}).pow_mem_of_mem (Ideal.subset_span (by simp)) 2 (by norm_num))
    · rw [hh]
      exact (Ideal.span {ϖ, j, j₂}).sub_mem (Ideal.subset_span (by simp))
        ((Ideal.span {ϖ, j, j₂}).pow_mem_of_mem (Ideal.subset_span (by simp)) 2 (by norm_num))

private theorem crossing_ideals_two_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hq2 : q = 2)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
      (∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))],
        IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
            ((0 : k) ^ q)) =
          Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K)
                (MvPolynomial.X 0 ^ 2 + 2608 * MvPolynomial.X 0 + 768 - MvPolynomial.X 1),
              modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
                  ((0 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
          ,
          (⟨modularEval (1 * q) (coeffSubring A K)
                (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2 + 1488 * MvPolynomial.X 1 + 3328),
              modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
                  ((0 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
          }) ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K)
                (MvPolynomial.X 0 ^ 2 + 2608 * MvPolynomial.X 0 + 768 - MvPolynomial.X 1),
              modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
                  ((0 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
          }).IsPrime ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K)
                (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2 + 1488 * MvPolynomial.X 1 + 3328),
              modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
                  ((0 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
          }).IsPrime ∧
          (⟨modularEval (1 * q) (coeffSubring A K)
                (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2 + 1488 * MvPolynomial.X 1 + 3328),
              modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
                  ((0 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
           ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K)
                (MvPolynomial.X 0 ^ 2 + 2608 * MvPolynomial.X 0 + 768 - MvPolynomial.X 1),
              modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
                  ((0 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
          } ∧
          (⟨modularEval (1 * q) (coeffSubring A K)
                (MvPolynomial.X 0 ^ 2 + 2608 * MvPolynomial.X 0 + 768 - MvPolynomial.X 1),
              modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
                  ((0 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
           ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K)
                (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2 + 1488 * MvPolynomial.X 1 + 3328),
              modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
                  ((0 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
          } ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K)
                (MvPolynomial.X 0 ^ 2 + 2608 * MvPolynomial.X 0 + 768 - MvPolynomial.X 1),
              modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
                  ((0 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
          } = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
            (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))} ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K)
                (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2 + 1488 * MvPolynomial.X 1 + 3328),
              modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
                  ((0 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
          } = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
            (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))} := by
  classical
  subst hq2

  obtain ⟨⟨hpg, hhg, -⟩, h₂⟩ :=
    isPrime_span_uniformizer_branches_modularLocalizedAtPoint (q := 2) red (0 : k) K ϖ hϖ
  obtain ⟨hph, hgh⟩ := h₂ (by norm_num)

  obtain ⟨-, hloc, -, hm⟩ :=
    isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring (q := 2) red (0 : k) K
      (0 : ↥(coeffSubring A K)) (map_zero _) ϖ hϖ

  obtain ⟨d, hd⟩ : ∃ d, ((2 : ℕ) : ↥(coeffSubring A K)) = ϖ * d :=
    (hϖ _).mp (by rw [map_natCast]; exact CharP.cast_eq_zero k 2)

  set φ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+*
      ↥(modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ 2)) :=
    (modularEval (1 * 2) (coeffSubring A K)).codRestrict _
      (modularEval_mem_modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k)
        ((0 : k) ^ 2)) with hφ
  have hC2 : (MvPolynomial.C ϖ : MvPolynomial (Fin 2) ↥(coeffSubring A K)) * MvPolynomial.C d = 2 := by
    rw [← MvPolynomial.C_mul, ← hd]; simp only [Nat.cast_ofNat, map_ofNat]
  haveI := hloc
  have key := crossing_ideals_of_branches
    (φ (MvPolynomial.C ϖ)) (φ (MvPolynomial.X 0 - MvPolynomial.C 0))
    (φ (MvPolynomial.X 1 - MvPolynomial.C (0 ^ 2)))
    (φ (MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2)) (φ (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2))
    (φ (MvPolynomial.X 0 ^ 2 + 2608 * MvPolynomial.X 0 + 768 - MvPolynomial.X 1))
    (φ (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2 + 1488 * MvPolynomial.X 1 + 3328))
    (φ (MvPolynomial.C d * (1304 * MvPolynomial.X 0 + 384)))
    (φ (MvPolynomial.C d * (744 * MvPolynomial.X 1 + 1664)))
    (by rw [← map_pow, ← map_sub]; exact congrArg φ (by simp))
    (by rw [← map_pow, ← map_sub]; exact congrArg φ (by simp))
    (by rw [← map_neg, ← map_mul, ← map_add]; congr 1
        linear_combination (-(1304 * MvPolynomial.X 0 + 384)) * hC2)
    (by rw [← map_mul, ← map_add]; congr 1
        linear_combination (-(744 * MvPolynomial.X 1 + 1664)) * hC2)
    hpg hph hhg hgh hm
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := key
  refine ⟨?_, k2, k3, k4, k5, k6, k7⟩
  intro inst
  rw [Subsingleton.elim inst hloc]
  exact k1

private theorem prefix_two {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k 2] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    ∃ (eK : ℕ) (ε : (↥(coeffSubring A K))ˣ), 1 ≤ eK ∧ ((2 : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε := by
  have h2 : redRestrict red K ((2 : ℕ) : ↥(coeffSubring A K)) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero k 2
  have h2ne : ((2 : ℕ) : ↥(coeffSubring A K)) ≠ 0 := by
    intro h
    have := congrArg (fun x : ↥(coeffSubring A K) => (x : AlgebraicClosure ℚ)) h
    simp at this
  have hϖ0 : redRestrict red K ϖ = 0 := (hϖ ϖ).2 ⟨1, (mul_one ϖ).symm⟩
  have hϖne : ϖ ≠ 0 := by
    rintro rfl
    obtain ⟨d, hd⟩ := (hϖ _).1 h2
    rw [zero_mul] at hd
    exact h2ne hd

  have hdvr : IsDiscreteValuationRing ↥(coeffSubring A K) := by
    rcases coeffSubring_eq_or_isDiscreteValuationRing A K with hK | h
    · exfalso
      have hmem : ∀ y : AlgebraicClosure ℚ, y ∈ coeffSubring A K ↔ y ∈ K := fun y => by
        rw [hK]; exact Iff.rfl
      have hinv : ((ϖ : AlgebraicClosure ℚ))⁻¹ ∈ coeffSubring A K := (hmem _).2 (K.inv_mem ((hmem _).1 ϖ.2))
      have hone : redRestrict red K 1 = 0 := by
        have : (1 : ↥(coeffSubring A K)) = ϖ * ⟨_, hinv⟩ := by
          apply Subtype.ext
          have : (ϖ : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖne (Subtype.ext h)
          simp [this]
        rw [this, map_mul, hϖ0, zero_mul]
      exact one_ne_zero ((map_one (redRestrict red K)).symm.trans hone)
    · exact h
  have hker : RingHom.ker (redRestrict red K) = Ideal.span {ϖ} := by
    ext c
    rw [RingHom.mem_ker, hϖ, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨d, rfl⟩; exact ⟨d, mul_comm d ϖ⟩
    · rintro ⟨d, rfl⟩; exact ⟨d, mul_comm d ϖ⟩
  have hprime : (Ideal.span {ϖ} : Ideal ↥(coeffSubring A K)).IsPrime := hker ▸ RingHom.ker_isPrime _
  have hmax : (Ideal.span {ϖ} : Ideal ↥(coeffSubring A K)).IsMaximal :=
    haveI := hprime
    IsPrime.to_maximal_ideal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hϖne)
  have hmax' : maximalIdeal ↥(coeffSubring A K) = Ideal.span {ϖ} := (IsLocalRing.eq_maximalIdeal hmax).symm
  have hirr : Irreducible ϖ := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ hϖne hmax'
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h2ne hirr
  refine ⟨n, u, ?_, by rw [hn, mul_comm]⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hpos
  · exfalso
    rw [hn0, pow_zero, mul_one] at hn
    have hu : IsUnit (redRestrict red K ((2 : ℕ) : ↥(coeffSubring A K))) := hn ▸ (u.isUnit.map _)
    rw [h2] at hu
    exact not_isUnit_zero hu
  · exact hpos

end PhiTwoNode
end ModularCurve

open ModularCurve.PhiTwoNode in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hq2 : q = 2)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    ∃ (eK : ℕ) (ε : ↥(coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧ ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε ∧
    ∃ (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
      IsUnit w ∧
      G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))) ^
              (autWeight 2 0 * eK) * w ∧
      (∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))],
        IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
            ((0 : k) ^ q)) =
          Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), G', H'}) ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
            G'}).IsPrime ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
            H'}).IsPrime ∧
      H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), G'} ∧
      G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), H'} ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
            G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
            (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))} ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
            H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
            (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k)
              ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))} := by
  haveI : DecidableEq k := Classical.decEq k
  subst hq2

  obtain ⟨eK, u, heK, h2⟩ := prefix_two red K ϖ hϖ
  refine ⟨eK, (u : ↥(coeffSubring A K)), heK, u.isUnit, h2, ?_⟩

  have hUne : modularEval (1 * 2) (coeffSubring A K)
      ((-38443359999 + 2133623 * MvPolynomial.X 0 - 41 * MvPolynomial.X 0 ^ 2)
              + (2135464 + 9007 * MvPolynomial.X 0) * MvPolynomial.X 1
              + (-39 + MvPolynomial.X 0) * MvPolynomial.X 1 ^ 2) ≠ 0 := fun h =>
    pointEval_cofactor_two_ne_zero red rfl K (pointEval_eq_zero_of_modularEval_eq_zero red (0 : k) K _ h)
  have hUmem : (modularEval (1 * 2) (coeffSubring A K)
      ((-38443359999 + 2133623 * MvPolynomial.X 0 - 41 * MvPolynomial.X 0 ^ 2)
              + (2135464 + 9007 * MvPolynomial.X 0) * MvPolynomial.X 1
              + (-39 + MvPolynomial.X 0) * MvPolynomial.X 1 ^ 2))⁻¹
      ∈ modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ 2) :=
    ⟨1, _, pointEval_cofactor_two_ne_zero red rfl K, by rw [inv_mul_cancel₀ hUne, map_one]⟩
  have hUunit : IsUnit
      (⟨modularEval (1 * 2) (coeffSubring A K)
        ((-38443359999 + 2133623 * MvPolynomial.X 0 - 41 * MvPolynomial.X 0 ^ 2)
              + (2135464 + 9007 * MvPolynomial.X 0) * MvPolynomial.X 1
              + (-39 + MvPolynomial.X 0) * MvPolynomial.X 1 ^ 2),
        modularEval_mem_modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k)
          ((0 : k) ^ 2) _⟩ :
        ↥(modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ 2))) :=
    isUnit_iff_exists_inv.2 ⟨⟨_, hUmem⟩, Subtype.ext (mul_inv_cancel₀ hUne)⟩

  have hεunit : IsUnit (⟨modularEval (1 * 2) (coeffSubring A K) (MvPolynomial.C (u : ↥(coeffSubring A K))),
        modularEval_mem_modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k)
          ((0 : k) ^ 2) _⟩ :
        ↥(modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ 2))) := by
    refine isUnit_iff_exists_inv.2
      ⟨⟨modularEval (1 * 2) (coeffSubring A K) (MvPolynomial.C (↑u⁻¹ : ↥(coeffSubring A K))),
        modularEval_mem_modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k)
          ((0 : k) ^ 2) _⟩, Subtype.ext ?_⟩
    change modularEval (1 * 2) (coeffSubring A K) (MvPolynomial.C (u : ↥(coeffSubring A K)))
        * modularEval (1 * 2) (coeffSubring A K) (MvPolynomial.C (↑u⁻¹ : ↥(coeffSubring A K))) = 1
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine
    ⟨(⟨modularEval (1 * 2) (coeffSubring A K)
        (MvPolynomial.X 0 ^ 2 + 2608 * MvPolynomial.X 0 + 768 - MvPolynomial.X 1),
        modularEval_mem_modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k)
          ((0 : k) ^ 2) _⟩ :
        ↥(modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ 2))),
      (⟨modularEval (1 * 2) (coeffSubring A K)
        (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2 + 1488 * MvPolynomial.X 1 + 3328),
        modularEval_mem_modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k)
          ((0 : k) ^ 2) _⟩ :
        ↥(modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ 2))),
    -((⟨modularEval (1 * 2) (coeffSubring A K) (MvPolynomial.C (u : ↥(coeffSubring A K))),
        modularEval_mem_modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k)
          ((0 : k) ^ 2) _⟩ :
        ↥(modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ 2))) ^ 12 *
      (⟨modularEval (1 * 2) (coeffSubring A K)
        ((-38443359999 + 2133623 * MvPolynomial.X 0 - 41 * MvPolynomial.X 0 ^ 2)
              + (2135464 + 9007 * MvPolynomial.X 0) * MvPolynomial.X 1
              + (-39 + MvPolynomial.X 0) * MvPolynomial.X 1 ^ 2),
        modularEval_mem_modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k)
          ((0 : k) ^ 2) _⟩ :
        ↥(modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ 2)))),
    ((hεunit.pow 12).mul hUunit).neg, ?_, crossing_ideals_two_zero red rfl K ϖ hϖ⟩

  have haw : autWeight 2 0 = 12 := by simp [autWeight]
  have hprod := modularEval_branchFactor_mul_branchFactor_two A K rfl
  have h2L : (2 : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * 2) (coeffSubring A K) (MvPolynomial.C ϖ) ^ eK
        * modularEval (1 * 2) (coeffSubring A K) (MvPolynomial.C (u : ↥(coeffSubring A K))) := by
    have := congrArg ((modularEval (1 * 2) (coeffSubring A K)).comp MvPolynomial.C) h2
    rw [map_natCast, map_mul, map_pow, RingHom.comp_apply, RingHom.comp_apply, Nat.cast_ofNat] at this
    exact this
  apply Subtype.ext
  simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_neg]
  rw [hprod, haw, h2L, pow_mul]
  ring

end
end S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_two
end P2MW
export P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_two (solution)

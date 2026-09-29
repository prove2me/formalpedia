-- Prove2me | solution 1 for ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1e0413be-2860-50e9-8736-e2fdfd92fd40

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_AlgebraicCurve_twelve_mul_eq_of_sum_ordDiff_eq
import Theorems.Thm_ModularCurve_sum_ord_jBar_sub_eq_dedekindPsi
import Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_eq_ordDifferential
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_jCoordinate_spec_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_sum_neg_ord_jBar_eq_dedekindPsi
import Definitions.Def_ModularCurve_EMD
import Definitions.Def_ModularCurve_ModuliPoint
import Theorems.Thm_ModularCurve_ord_jBar_dvd_three
import Theorems.Thm_ModularCurve_ord_jBar_sub_1728_dvd_two
import Theorems.Thm_ModularCurve_ord_jBar_sub_eq_one_of_ne_zero_of_ne
import Theorems.Thm_ModularCurve_card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg
import Theorems.Thm_ModularCurve_natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo
import Theorems.Thm_ModularCurve_natCard_ord_jBar_eq_one_eq_nuThree
import Theorems.Thm_ModularCurve_card_eq_natCard_moduliPoint_j_eq_of_EMD
import Theorems.Thm_ModularCurve_emd_holds
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open ModularCurve AlgebraicCurve IntermediateField

theorem solution (N : ℕ) [NeZero N]
    [AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.modularFunctionFieldBar N))] :
    (AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℚ)
      = ModularCurve.genusFormula N := by
  classical

  set F := ↥(modularFunctionFieldBar N) with hF
  set j : ↥(modularFunctionFieldBar N) := jBar N with hj
  have hjdef : j = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : ↥(modularFunctionFieldBar N)) := rfl
  have h1728 : (j - 1728 : ↥(modularFunctionFieldBar N))
      = j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728 := by
    rw [map_ofNat]

  haveI : CharZero ↥(modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := IsCurveOver.hasPrincipalDivisors
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    essFiniteType_modularFunctionFieldBar N
  haveI hfd : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N) := finiteDimensional_adjoin_coeffEmb_jq_of_neZero N
  haveI : CharZero ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set ↥(modularFunctionFieldBar N))) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  haveI : PerfectField ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set ↥(modularFunctionFieldBar N))) :=
    PerfectField.ofCharZero
  haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N) := Algebra.IsSeparable.of_integral _ _
  have htr : Transcendental (AlgebraicClosure ℚ) j := transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N

  have hdeg : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), w.deg = 1 :=
    deg_eq_one_modularFunctionFieldBar N

  obtain ⟨hval, hfinc, hfinI⟩ := jCoordinate_spec_modularFunctionFieldBar N

  set S0 : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) := (hfinc 0).toFinset with hS0def
  set S1 : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) := (hfinc 1728).toFinset with hS1def
  set Sinf : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) := hfinI.toFinset with hSIdef
  have hS0 : ∀ v, v ∈ S0 ↔ 0 < v.ord j := fun v => by
    rw [hS0def, Set.Finite.mem_toFinset, Set.mem_setOf_eq, map_zero, sub_zero]
  have hS1 : ∀ v, v ∈ S1 ↔ 0 < v.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728) :=
    fun v => by rw [hS1def, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hSI : ∀ v, v ∈ Sinf ↔ v.ord j < 0 := fun v => by
    rw [hSIdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

  have hDj1728 : KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j
      = KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)
          (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728) := by
    rw [map_sub, Derivation.map_algebraMap, sub_zero]
  have h₀ : ∀ v ∈ S0, v.ordDiff (KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j) = v.ord j - 1
      ∧ 0 < v.ord j ∧ v.ord j ∣ 3 := fun v hv => by
    have hpos := (hS0 v).1 hv
    exact ⟨AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one j v hpos.ne', hpos, ord_jBar_dvd_three N v hpos⟩
  have h₁ : ∀ v ∈ S1,
      v.ordDiff (KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j)
        = v.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728) - 1
      ∧ 0 < v.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728)
      ∧ v.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728) ∣ 2 := fun v hv => by
    have hpos := (hS1 v).1 hv
    refine ⟨?_, hpos, ord_jBar_sub_1728_dvd_two N v hpos⟩
    rw [hDj1728]
    exact AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one j v hpos.ne'
  have hinf : ∀ v ∈ Sinf, v.ordDiff (KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j) = v.ord j - 1
      ∧ v.ord j < 0 := fun v hv => by
    have hneg := (hSI v).1 hv
    exact ⟨AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one j v hneg.ne, hneg⟩

  have hψ₀ : ∑ v ∈ S0, v.ord j = (dedekindPsi N : ℤ) := by
    have h := sum_ord_jBar_sub_eq_dedekindPsi N 0 hdeg S0 (fun v => by rw [hS0, map_zero, sub_zero])
    simpa [map_zero, sub_zero] using h
  have hψ₁ : ∑ v ∈ S1, v.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728) = (dedekindPsi N : ℤ) :=
    sum_ord_jBar_sub_eq_dedekindPsi N 1728 hdeg S1 hS1
  have hψinf : ∑ v ∈ Sinf, -v.ord j = (dedekindPsi N : ℤ) := sum_neg_ord_jBar_eq_dedekindPsi N Sinf hSI

  set S := S0 ∪ S1 ∪ Sinf with hSdef
  have hS : ∀ v, v ∈ S ↔ v ∈ S0 ∨ v ∈ S1 ∨ v ∈ Sinf := fun v => by
    simp only [hSdef, Finset.mem_union, or_assoc]
  have hDj : KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental (AlgebraicClosure ℚ) j htr

  have hoff : ∀ v, v ∉ S → v.ordDiff (KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j) = 0 := by
    intro v hv
    rw [hS] at hv
    push Not at hv
    obtain ⟨hv0, hv1, hvI⟩ := hv
    have hnonneg : 0 ≤ v.ord j := by
      by_contra h
      exact hvI ((hSI v).2 (lt_of_not_ge h))
    obtain ⟨c, hcpos, -⟩ := hval v hnonneg
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hv0
      rw [hS0]
      simpa [map_zero, sub_zero] using hcpos
    have hc1728 : c ≠ 1728 := by
      rintro rfl
      exact hv1 ((hS1 v).2 hcpos)
    have hone := ord_jBar_sub_eq_one_of_ne_zero_of_ne N v c hc0 hc1728 hcpos
    have hD : KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j
        = KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)
            (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c) := by
      rw [map_sub, Derivation.map_algebraMap, sub_zero]
    rw [hD, AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one j v (by rw [hone]; exact one_ne_zero), hone]
    norm_num
  have hcan : ∑ v ∈ S, v.ordDiff (KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j)
      = 2 * (genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) - 2 := by
    rw [← degree_canonicalDivisorOf_modularFunctionFieldBar N hDj]
    set Kd := canonicalDivisorOf hDj with hKd
    have hseam : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
        v.ordDiff (KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j) = Kd v := fun v => by
      rw [hKd, canonicalDivisorOf_apply, AlgebraicCurve.Place.ordDiff_eq_ordDifferential]
    have hsupp : Kd.support ⊆ S := by
      intro v hv
      by_contra hvS
      rw [Finsupp.mem_support_iff] at hv
      exact hv ((hseam v).symm.trans (hoff v hvS))
    have hdegsum : Divisor.degree Kd = ∑ v ∈ Kd.support, Kd v := by
      rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [AddMonoidHom.mulRight_apply, hdeg v, Nat.cast_one, mul_one]
    rw [hdegsum, Finset.sum_subset hsupp (fun v _ hv => by simpa [Finsupp.mem_support_iff] using hv)]
    exact Finset.sum_congr rfl (fun v _ => hseam v)

  have hHE := AlgebraicCurve.twelve_mul_eq_of_sum_ordDiff_eq j S0 S1 Sinf (dedekindPsi N)
    (genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) h₀ h₁ hinf hψ₀ hψ₁ hψinf S hS hcan

  have hNC : ∀ (P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) → Prop)
      (T : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))),
      (∀ v, v ∈ T ↔ P v) → Nat.card {v // P v} = T.card := by
    intro P T hT
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun v => (hT v).symm) : {v // P v} ≃ {v // v ∈ T}),
      Nat.card_eq_fintype_card, Fintype.card_coe]
  have hε₂ : (S1.filter fun v => v.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728) = 1).card
      = nuTwo N := by
    have h2 : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
        0 < v.ord (jBar N - 1728) → v.ord (jBar N - 1728) ∣ 2 := fun v hv => by
      rw [← hj, h1728] at hv ⊢
      exact ord_jBar_sub_1728_dvd_two N v hv
    have hcount : Nat.card {v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) // 0 < v.ord (jBar N - 1728)}
        = Nat.card {x : ModuliPoint N (AlgebraicClosure ℚ) // ModuliPoint.j x = (1728 : AlgebraicClosure ℚ)} := by
      rw [← card_eq_natCard_moduliPoint_j_eq_of_EMD N 1728 (emd_holds N 1728) S1 hS1]
      exact hNC _ S1 (fun v => by rw [hS1, ← hj, h1728])
    have h := natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo N h2 hcount
    rwa [hNC _ (S1.filter fun v => v.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728) = 1)
      (fun v => by
        rw [Finset.mem_filter, hS1, ← hj, h1728]
        exact ⟨fun hv => hv.2, fun hv => ⟨by rw [hv]; exact one_pos, hv⟩⟩)] at h
  have hε₃ : (S0.filter fun v => v.ord j = 1).card = nuThree N := by
    have h3 : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
        0 < v.ord (jBar N) → v.ord (jBar N) ∣ 3 := fun v hv => ord_jBar_dvd_three N v hv
    have hcount : Nat.card {v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) // 0 < v.ord (jBar N)}
        = Nat.card {x : ModuliPoint N (AlgebraicClosure ℚ) // ModuliPoint.j x = (0 : AlgebraicClosure ℚ)} := by
      rw [← card_eq_natCard_moduliPoint_j_eq_of_EMD N 0 (emd_holds N 0) S0 (fun v => by rw [hS0, hj, map_zero, sub_zero])]
      exact hNC _ S0 (fun v => by rw [hS0, hj])
    have h := natCard_ord_jBar_eq_one_eq_nuThree N h3 hcount
    rwa [hNC _ (S0.filter fun v => v.ord j = 1)
      (fun v => by
        rw [Finset.mem_filter, hS0, hj]
        exact ⟨fun hv => hv.2, fun hv => ⟨by rw [hv]; exact one_pos, hv⟩⟩)] at h

  have hcard : Sinf.card = cuspCount N := card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg N Sinf hSI
  rw [hε₂, hε₃, hcard] at hHE

  have key : (12 : ℚ) * (genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℚ)
      = 12 + (dedekindPsi N : ℚ) - 3 * (nuTwo N : ℚ) - 4 * (nuThree N : ℚ) - 6 * (cuspCount N : ℚ) := by
    exact_mod_cast hHE
  unfold genusFormula
  linarith [key]

end S_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula
end P2MW
export P2MW.S_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula (solution)

-- Prove2me | solution 1 for ModularCurve.MultCovering.infChart_chartData_goodFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/bcf97732-7888-55ba-8c52-e752670a8fcd

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_exists_chartData_of_lineResidues
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_MultCovering_cuspInftyBar_mem_infChart_dom
import Theorems.Thm_ModularCurve_MultCovering_eq_mAnnuli_add_one_of_isEmbBasis
import Theorems.Thm_ModularCurve_LevelOneFibre_card_eq_genusFF_one_mul_add_one_of_ssJSet
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_infChart_chartData_goodFamily
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.cuspCount_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~jBar P2MW.S_ModularCurve_MultCovering_infChart_chartData_goodFamily.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_infChart_chartData_goodFamily.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "embDegree embDivisor cuspInftyBar modularFunctionFieldBar ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun modularFunctionFieldC PlaceSpecialization charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC PlaceSpecialization.LevelOneProlongationPair.ChartFst.residue₁_ne_zero_iff mem_ssPlaces_iff exists_chartData_of_lineResidues hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCurveOver_modularFunctionFieldBar LevelOneFibre.card_eq_genusFF_one_mul_add_one_of_ssJSet"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "ssPolyBar FamCtx goodFamily jBar mAnnuli ChartCtx infChart chart ssValue ssValue_mem_ssJSet cuspInftyBar_mem_infChart_dom eq_mAnnuli_add_one_of_isEmbBasis"
namespace LineAlg
p2m_open "ModularCurve.MultCovering ModularCurve~jBar"

open Polynomial

variable {K : Type*} [Field K]

theorem forall_mem_span_of_forall {ι : Type*} (P : ι → K[X]) (φ : K[X] →ₗ[K] K)
    (h : ∀ l, φ (P l) = 0) : ∀ Q ∈ Submodule.span K (Set.range P), φ Q = 0 := by
  intro Q hQ
  induction hQ using Submodule.span_induction with
  | mem x hx => obtain ⟨l, rfl⟩ := hx; exact h l
  | zero => exact map_zero φ
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

theorem one_mem_degreeLT {m : ℕ} (hm : 1 ≤ m) : (1 : K[X]) ∈ Polynomial.degreeLT K m := by
  rw [Polynomial.mem_degreeLT]
  exact lt_of_le_of_lt degree_one_le (by exact_mod_cast hm)

theorem X_mem_degreeLT {m : ℕ} (hm : 2 ≤ m) : (X : K[X]) ∈ Polynomial.degreeLT K m := by
  rw [Polynomial.mem_degreeLT]
  exact lt_of_le_of_lt degree_X_le (by exact_mod_cast hm)

theorem X_pow_mem_degreeLT {m n : ℕ} (h : n < m) : (X ^ n : K[X]) ∈ Polynomial.degreeLT K m := by
  rw [Polynomial.mem_degreeLT]
  exact lt_of_le_of_lt (degree_X_pow_le n) (by exact_mod_cast h)

theorem exists_eval_ne_zero {ι : Type*} {m : ℕ} (hm : 1 ≤ m) (P : ι → K[X])
    (hspan : Submodule.span K (Set.range P) = Polynomial.degreeLT K m) (x₀ : K) :
    ∃ l, (P l).eval x₀ ≠ 0 := by
  by_contra h
  push_neg at h
  have key := forall_mem_span_of_forall P (Polynomial.leval x₀) (fun l => by simpa using h l) 1
    (by rw [hspan]; exact one_mem_degreeLT hm)
  simp at key

theorem exists_eval_mul_ne {ι : Type*} {m : ℕ} (hm : 1 ≤ m) (P : ι → K[X])
    (hspan : Submodule.span K (Set.range P) = Polynomial.degreeLT K m)
    (SS : K[X]) (hSS : SS.Monic) (hdeg : SS.natDegree = m)
    {x₀ y₀ : K} (hxy : x₀ ≠ y₀) (hx : SS.eval x₀ ≠ 0) :
    ∃ l, SS.eval x₀ * (P l).eval x₀ ≠ SS.eval y₀ * (P l).eval y₀ := by
  by_contra h
  push_neg at h

  let φ : K[X] →ₗ[K] K := SS.eval x₀ • Polynomial.leval x₀ - SS.eval y₀ • Polynomial.leval y₀
  have hφ : ∀ Q : K[X], φ Q = SS.eval x₀ * Q.eval x₀ - SS.eval y₀ * Q.eval y₀ := fun Q => by
    simp [φ, Polynomial.leval_apply]
  have hall := forall_mem_span_of_forall P φ (fun l => by rw [hφ, h l, sub_self])
  have h1 : SS.eval x₀ = SS.eval y₀ := by
    have := hall 1 (by rw [hspan]; exact one_mem_degreeLT hm)
    rw [hφ] at this
    simp only [eval_one, mul_one] at this
    exact sub_eq_zero.mp this
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  ·
    have hm1' : m = 1 := by omega
    subst hm1'
    have hSS : SS = X + C (SS.coeff 0) := hSS.eq_X_add_C hdeg
    have : x₀ = y₀ := by
      have h2 := h1
      rw [hSS] at h2
      simpa using h2
    exact hxy this
  · have := hall X (by rw [hspan]; exact X_mem_degreeLT hm2)
    rw [hφ, eval_X, eval_X, ← h1, ← mul_sub, mul_eq_zero, sub_eq_zero] at this
    rcases this with h0 | h0
    · exact hx h0
    · exact hxy h0

theorem exists_derivative_eval_ne_zero {ι : Type*} {m : ℕ} (hm : 1 ≤ m) (P : ι → K[X])
    (hspan : Submodule.span K (Set.range P) = Polynomial.degreeLT K m)
    (SS : K[X]) (hSS : SS.Monic) (hdeg : SS.natDegree = m)
    {x₀ : K} (hx : SS.eval x₀ ≠ 0) :
    ∃ l, (derivative (SS * P l)).eval x₀ ≠ 0 := by
  by_contra h
  push_neg at h
  let φ : K[X] →ₗ[K] K := (Polynomial.leval x₀).comp ((Polynomial.derivative).comp (LinearMap.mulLeft K SS))
  have hφ : ∀ Q : K[X], φ Q = (derivative (SS * Q)).eval x₀ := fun Q => rfl
  have hall := forall_mem_span_of_forall P φ (fun l => by rw [hφ]; exact h l)
  have h1 : (derivative SS).eval x₀ = 0 := by
    have := hall 1 (by rw [hspan]; exact one_mem_degreeLT hm)
    rwa [hφ, mul_one] at this
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · have hm1' : m = 1 := by omega
    subst hm1'
    rw [hSS.eq_X_add_C hdeg] at h1
    simp at h1
  · have := hall X (by rw [hspan]; exact X_mem_degreeLT hm2)
    rw [hφ, derivative_mul, derivative_X, mul_one, eval_add, eval_mul, h1, zero_mul, zero_add] at this
    exact hx this

theorem exists_natDegree_eq {ι : Type*} {m : ℕ} (hm : 1 ≤ m) (P : ι → K[X])
    (hspan : Submodule.span K (Set.range P) = Polynomial.degreeLT K m) :
    ∃ l, (P l).natDegree = m - 1 := by
  by_contra h
  push_neg at h

  have hle : ∀ l, P l ∈ Polynomial.degreeLT K (m - 1) := by
    intro l
    rw [Polynomial.mem_degreeLT]
    have hlt : (P l).degree < m := by
      rw [← Polynomial.mem_degreeLT, ← hspan]; exact Submodule.subset_span ⟨l, rfl⟩
    by_cases h0 : P l = 0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree h0] at hlt ⊢
      have : (P l).natDegree < m := by exact_mod_cast hlt
      have : (P l).natDegree < m - 1 := by have := h l; omega
      exact_mod_cast this
  have hspan' : Submodule.span K (Set.range P) ≤ Polynomial.degreeLT K (m - 1) :=
    Submodule.span_le.mpr (by rintro _ ⟨l, rfl⟩; exact hle l)
  have hX : (X ^ (m - 1) : K[X]) ∈ Polynomial.degreeLT K m := X_pow_mem_degreeLT (by omega)
  rw [← hspan] at hX
  have := hspan' hX
  rw [Polynomial.mem_degreeLT, degree_X_pow] at this
  exact lt_irrefl _ (by exact_mod_cast this)

theorem exists_natDegree_sub_eq {ι : Type*} {m : ℕ} (hm : 2 ≤ m) (P : ι → K[X])
    (hspan : Submodule.span K (Set.range P) = Polynomial.degreeLT K m)
    (c : ι) (hc : (P c).natDegree = m - 1) (hc0 : P c ≠ 0) :
    ∃ j, P j - C ((P j).coeff (m - 1) / (P c).leadingCoeff) * P c ≠ 0 ∧
      (P j - C ((P j).coeff (m - 1) / (P c).leadingCoeff) * P c).natDegree = m - 2 := by
  have hlc : (P c).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hc0
  have hlc' : (P c).coeff (m - 1) = (P c).leadingCoeff := by rw [Polynomial.leadingCoeff, hc]

  let π : K[X] →ₗ[K] K[X] :=
    LinearMap.id - LinearMap.smulRight (Polynomial.lcoeff K (m - 1)) ((P c).leadingCoeff⁻¹ • P c)
  have hπ : ∀ Q : K[X], π Q = Q - C (Q.coeff (m - 1) / (P c).leadingCoeff) * P c := by
    intro Q
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, Polynomial.lcoeff_apply,
      smul_smul, Polynomial.C_mul', div_eq_mul_inv]
  have hπlt : ∀ Q ∈ Polynomial.degreeLT K m, π Q ∈ Polynomial.degreeLT K (m - 1) := by
    intro Q hQ
    rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero] at hQ ⊢
    intro k hk
    rw [hπ, coeff_sub, coeff_C_mul]
    rcases Nat.lt_or_ge k m with hkm | hkm
    · have hk' : k = m - 1 := by omega
      subst hk'
      rw [hlc', div_mul_cancel₀ _ hlc, sub_self]
    · rw [hQ k hkm]
      have h0 : (P c).coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt; omega
      rw [h0, mul_zero, sub_zero]
  have hπfix : ∀ Q ∈ Polynomial.degreeLT K (m - 1), π Q = Q := by
    intro Q hQ
    rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero] at hQ
    rw [hπ, hQ (m - 1) le_rfl, zero_div, C_0, zero_mul, sub_zero]
  by_contra h
  push_neg at h
  have hsmall : ∀ j, π (P j) ∈ Polynomial.degreeLT K (m - 2) := by
    intro j
    have hj : π (P j) ∈ Polynomial.degreeLT K (m - 1) :=
      hπlt _ (by rw [← hspan]; exact Submodule.subset_span ⟨j, rfl⟩)
    rw [Polynomial.mem_degreeLT] at hj ⊢
    by_cases h0 : π (P j) = 0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree h0] at hj ⊢
      have h1 : (π (P j)).natDegree < m - 1 := by exact_mod_cast hj
      have h2 : (π (P j)).natDegree ≠ m - 2 := by
        have h0' : P j - C ((P j).coeff (m - 1) / (P c).leadingCoeff) * P c ≠ 0 := by rw [← hπ]; exact h0
        rw [hπ]; exact h j h0'
      exact_mod_cast (show (π (P j)).natDegree < m - 2 by omega)
  have hmap : ∀ Q ∈ Submodule.span K (Set.range P), π Q ∈ Polynomial.degreeLT K (m - 2) := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hsmall j
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hX : (X ^ (m - 2) : K[X]) ∈ Submodule.span K (Set.range P) := by
    rw [hspan]; exact X_pow_mem_degreeLT (by omega)
  have h1 := hmap _ hX
  rw [hπfix _ (X_pow_mem_degreeLT (by omega)), Polynomial.mem_degreeLT, degree_X_pow] at h1
  exact lt_irrefl _ (by exact_mod_cast h1)

end ModularCurve.MultCovering.LineAlg

namespace ModularCurve
p2m_export "ModularCurve" "embDegree embDivisor cuspInftyBar modularFunctionFieldBar ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun modularFunctionFieldC PlaceSpecialization charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC PlaceSpecialization.LevelOneProlongationPair.ChartFst.residue₁_ne_zero_iff mem_ssPlaces_iff exists_chartData_of_lineResidues hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCurveOver_modularFunctionFieldBar LevelOneFibre.card_eq_genusFF_one_mul_add_one_of_ssJSet"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "ssPolyBar FamCtx goodFamily jBar mAnnuli ChartCtx infChart chart ssValue ssValue_mem_ssJSet cuspInftyBar_mem_infChart_dom eq_mAnnuli_add_one_of_isEmbBasis"
p2m_open "ModularCurve.MultCovering ModularCurve~jBar"

open Polynomial in

theorem aeval_jBar_injective_ord (k : Type) [Field k] :
    Function.Injective (Polynomial.aeval (R := k) (jBar k)) := by
  have htr : Transcendental k (jBar k) :=
    (transcendental_algebraMap_iff
      (algebraMap (↥(modularFunctionFieldC k 1)) (LaurentSeries k)).injective).mp (transcendental_jqModC k)
  exact transcendental_iff_injective.mp htr

open Classical in
theorem mem_infChart_dom_and_placeMap_eq_placeInfty_iff
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))]
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) :
    (W ∈ (infChart Γ).dom ∧ (infChart Γ).placeMap W
        = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))) ↔
      Γ.P.IsInftySide W := by
  rw [← Γ.P.redFst_cuspInftyBar]
  show (W ∈ (infChart Γ).dom ∧ Γ.P.redFst W = Γ.P.redFst (cuspInftyBar (1 * p))) ↔ _
  constructor
  · rintro ⟨hW, hred⟩
    have hW' : Γ.P.IsStrictTypeOne W ∨ Γ.P.IsInftySide W ∨ W ∈ Γ.S₁ := hW
    rcases hW' with h | h | h
    ·
      exact (h.2 (hred ▸ Γ.supply.cusp_fixed)).elim
    · exact h
    ·
      exact (((Γ.supply.isAffineGeomPlace_iff _).mp (Γ.supply.sheet.sheet_affine W h)) hred).elim
  · intro h
    exact ⟨Or.inr (Or.inl h), Γ.supply.redFst_eq_of_isInftySide W h⟩

open Classical in

theorem filter_mem_infChart_dom_and_placeMap_eq_placeInfty_eq_filter_isInftySide
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))]
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) :
    (E.filter (fun W => W ∈ (infChart Γ).dom ∧ (infChart Γ).placeMap W
        = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))))
      = E.filter Γ.P.IsInftySide := by
  classical
  ext W
  simp only [Finsupp.filter_apply, mem_infChart_dom_and_placeMap_eq_placeInfty_iff Γ W]

end ModularCurve.MultCovering

set_option maxHeartbeats 12800000 in
open Polynomial in

theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r) :

    ∃ (hint : ∀ i, goodFamily Φ i ∈ (infChart Γ).integers)
      (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
        → Fin r),
      (∀ P ∈ (infChart Γ).dom, P.IsRational ∧ ((infChart Γ).placeMap P).IsRational) ∧
      (∀ P ∈ (infChart Γ).dom,
        (infChart Γ).residue ⟨goodFamily Φ (cQ ((infChart Γ).placeMap P)), hint _⟩ ≠ 0) ∧
      (∀ P ∈ (infChart Γ).dom, ∀ j,
        goodFamily Φ j * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹
          ∈ (infChart Γ).integers) ∧
      (∀ P ∈ (infChart Γ).dom, ∀ j,
        goodFamily Φ j * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹
          ∈ P.toValuationSubring) ∧
      (∀ P ∈ (infChart Γ).dom,
        ∀ hmem : goodFamily Φ (iQ ((infChart Γ).placeMap P))
            * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹ ∈ (infChart Γ).integers,
        ((infChart Γ).placeMap P).ord ((infChart Γ).residue ⟨_, hmem⟩
          - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
              (((infChart Γ).placeMap P).evalAt ((infChart Γ).residue ⟨_, hmem⟩))) = 1) ∧
      (∀ P ∈ (infChart Γ).dom, ∀ Q ∈ (infChart Γ).dom,
        (infChart Γ).placeMap P ≠ (infChart Γ).placeMap Q →
        ∀ (hmP : ∀ j, goodFamily Φ j
              * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹ ∈ (infChart Γ).integers)
          (hmQ : ∀ j, goodFamily Φ j
              * (goodFamily Φ (cQ ((infChart Γ).placeMap Q)))⁻¹ ∈ (infChart Γ).integers),
        ∃ i j, ((infChart Γ).placeMap P).evalAt ((infChart Γ).residue ⟨_, hmP i⟩)
            * ((infChart Γ).placeMap Q).evalAt ((infChart Γ).residue ⟨_, hmQ j⟩)
          ≠ ((infChart Γ).placeMap P).evalAt ((infChart Γ).residue ⟨_, hmP j⟩)
            * ((infChart Γ).placeMap Q).evalAt ((infChart Γ).residue ⟨_, hmQ i⟩)) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P ∈ (infChart Γ).dom, ∃ l : Fin r, 1 ≤ (l : ℕ) ∧
          μ (P.evalAt (goodFamily Φ l
            * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹)) = 1) := by
  classical
  haveI hκ : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)

  have hFrat : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), v.IsRational := fun v => by
    haveI := ModularCurve.isCurveOver_modularFunctionFieldBar (1 * p)
    haveI : Module.Finite (AlgebraicClosure ℚ) v.ResidueField := IsCurveOver.finiteResidue v
    intro x
    have hxint : IsIntegral (AlgebraicClosure ℚ) x := IsIntegral.of_finite (AlgebraicClosure ℚ) x
    have h1 : (minpoly (AlgebraicClosure ℚ) x).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible (AlgebraicClosure ℚ) (minpoly.irreducible hxint)
    have hmem : x ∈ (algebraMap (AlgebraicClosure ℚ) v.ResidueField).range := by
      first
        | exact minpoly.mem_range_of_degree_eq_one (AlgebraicClosure ℚ) x h1
        | exact minpoly.mem_range_of_degree_eq_one _ h1
        | exact minpoly.mem_range_of_degree_eq_one h1
    exact RingHom.mem_range.mp hmem

  obtain ⟨hint, h0, P, hP, hli, hspan⟩ := Φ.t_inf A hA Γ

  have hcardg := ModularCurve.LevelOneFibre.card_eq_genusFF_one_mul_add_one_of_ssJSet hp5 Γ.hfin.toFinset
    (fun a => Set.Finite.mem_toFinset _)
  have hmg : mAnnuli p = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) + 1 := by rw [← Γ.hcard, hcardg]
  have hm : 1 ≤ mAnnuli p := by rw [hmg]; omega
  have hr : r = mAnnuli p + 1 := eq_mAnnuli_add_one_of_isEmbBasis p hp5 Φ.t Φ.t_basis
  have hr0 : 0 < r := by omega
  set l₀ : Fin r := ⟨0, hr0⟩ with hl₀
  have hembDeg : embDegree (1 * p) = 2 * mAnnuli p - 1 := by unfold embDegree; omega

  set m := mAnnuli p with hmdef
  set SS : (IsLocalRing.ResidueField ↥A)[X] := ∏ e : Fin (mAnnuli p), (X - C (ssValue Γ e)) with hSSdef
  have hSSmonic : SS.Monic := monic_prod_of_monic _ _ (fun e _ => monic_X_sub_C _)
  have hSSdeg : SS.natDegree = m := by
    rw [hSSdef, natDegree_prod_of_monic _ _ (fun e _ => monic_X_sub_C _)]
    simp [hmdef]
  have hSS0 : SS ≠ 0 := hSSmonic.ne_zero
  have hSSeval : ∀ x, SS.eval x = ∏ e : Fin (mAnnuli p), (x - ssValue Γ e) := fun x => by
    rw [hSSdef, eval_prod]; simp
  have hSSne : ∀ x, x ∉ ssJSet p (IsLocalRing.ResidueField ↥A) → SS.eval x ≠ 0 := by
    intro x hx
    rw [hSSeval, Finset.prod_ne_zero_iff]
    intro e _ h
    exact hx (sub_eq_zero.mp h ▸ ssValue_mem_ssJSet Γ e)
  have hSSaeval : aeval (jBar (IsLocalRing.ResidueField ↥A)) SS = ssPolyBar Γ := by
    rw [hSSdef, map_prod]
    show _ = ∏ e : Fin (mAnnuli p), (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e))
    refine Finset.prod_congr rfl (fun e _ => ?_)
    rw [map_sub, aeval_X, aeval_C]
  have hssPolyBar0 : ssPolyBar Γ ≠ 0 := by
    rw [← hSSaeval]; exact (map_ne_zero_iff _ (aeval_jBar_injective_ord _)).mpr hSS0

  set Rf : Fin r → (IsLocalRing.ResidueField ↥A)[X] := fun l => if (l : ℕ) = 0 then 1 else SS * P l with hRfdef
  have hRf0 : ∀ l : Fin r, (l : ℕ) = 0 → Rf l = 1 := fun l hl => by simp [hRfdef, hl]
  have hRf1 : ∀ l : Fin r, 1 ≤ (l : ℕ) → Rf l = SS * P l := fun l hl => by
    have : (l : ℕ) ≠ 0 := by omega
    simp [hRfdef, this]
  have hRfl₀ : Rf l₀ = 1 := hRf0 l₀ rfl
  have hunit : ∀ l, (infChart Γ).residue ⟨Φ.t l, hint l⟩ ≠ 0 := by
    intro l
    rcases Nat.eq_zero_or_pos (l : ℕ) with hl | hl
    · rw [h0 l hl]; exact one_ne_zero
    · rw [(hP l hl).2]
      exact mul_ne_zero hssPolyBar0
        ((map_ne_zero_iff _ (aeval_jBar_injective_ord _)).mpr (hli.ne_zero ⟨l, hl⟩))
  have hR : ∀ l, ((infChart Γ).residue ⟨Φ.t l, hint l⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) *
      Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (1 : (IsLocalRing.ResidueField ↥A)[X]) = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (Rf l) := by
    intro l
    rw [map_one, mul_one]
    rcases Nat.eq_zero_or_pos (l : ℕ) with hl | hl
    · rw [h0 l hl, hRf0 l hl, map_one]
    · rw [(hP l hl).2, hRf1 l hl, map_mul, hSSaeval]

  set P' : {l : Fin r // 1 ≤ (l : ℕ)} → (IsLocalRing.ResidueField ↥A)[X] := fun l => P l with hP'def
  have hspan' : Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range P') = Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) m := hspan

  have hnotss : ∀ Q ∈ (infChart Γ).dom, ∀ x₀, (infChart Γ).placeMap Q = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      x₀ ∉ ssJSet p (IsLocalRing.ResidueField ↥A) := by
    intro Q hQ x₀ hx hss
    apply (infChart Γ).placeMap_not_mem_nodes Q hQ
    show (infChart Γ).placeMap Q ∈ Γ.Wn
    rw [Γ.hWn, hx]
    exact (Γ.supply.mem_ssPlaces_iff _).mpr ⟨x₀, hss, rfl⟩

  have hc₀ : cuspInftyBar (1 * p) ∈ (infChart Γ).dom := cuspInftyBar_mem_infChart_dom Γ
  have hc₀inf : (infChart Γ).placeMap (cuspInftyBar (1 * p)) =
      charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) := by
    show Γ.P.redFst (cuspInftyBar (1 * p)) = _
    rw [Γ.P.redFst_cuspInftyBar]

  have hmemRR : ∀ l, Φ.t l ∈ riemannRochSpace (embDivisor (1 * p)) := fun l => by
    rw [← Φ.t_basis.2]; exact Submodule.subset_span ⟨l, rfl⟩
  have hembApp : ∀ W, embDivisor (1 * p) W = if W = cuspInftyBar (1 * p) then (embDegree (1 * p) : ℤ) else 0 := by
    intro W
    show ((embDegree (1 * p) : ℤ) • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ)) W = _
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    by_cases h : W = cuspInftyBar (1 * p)
    · rw [if_pos h.symm, if_pos h, mul_one]
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  have hreg₀ : ∀ Q ∈ (infChart Γ).dom, Q ≠ cuspInftyBar (1 * p) → ∀ l, Φ.t l ∈ Q.toValuationSubring := by
    intro Q _ hQ l
    by_cases h0 : Φ.t l = 0
    · rw [h0]; exact Subring.zero_mem _
    · rcases (mem_riemannRochSpace_iff.mp (hmemRR l)) Q with h | h
      · exact (h0 h).elim
      · rw [hembApp, if_neg hQ, neg_zero] at h
        exact Q.mem_of_ord_nonneg h0 h

  have hdom : ∀ Q ∈ (infChart Γ).dom,
      (∃ x₀ : (IsLocalRing.ResidueField ↥A), (infChart Γ).placeMap Q = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ ∧ (1 : (IsLocalRing.ResidueField ↥A)[X]).eval x₀ ≠ 0) ∨
        (infChart Γ).placeMap Q = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) := by
    intro Q _
    by_cases hex : ∃ a : ↥A, 0 < Q.ord (PlaceSpecialization.jFun (q := p)
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ))
    · obtain ⟨a, ha⟩ := hex
      left
      refine ⟨IsLocalRing.residue ↥A a, ?_, by rw [eval_one]; exact one_ne_zero⟩
      show Γ.P.redFst Q = _
      exact (Γ.supply.redFst_eq_charLGeomPlaceOfPoint_iff Q _).mpr ⟨a, rfl, ha⟩
    · right
      push_neg at hex
      show Γ.P.redFst Q = _
      exact Γ.P.redFst_eq_placeInfty_of_forall_ord_le_zero Q hex

  have hcusp : ∀ (f : ↥(modularFunctionFieldBar (1 * p))) (hf : f ∈ (infChart Γ).integers), (infChart Γ).residue ⟨f, hf⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), (∀ W, E W = W.ord f) →
        Finsupp.mapDomain (infChart Γ).placeMap
            (E.filter (fun W => W ∈ (infChart Γ).dom ∧ (infChart Γ).placeMap W =
              charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))))
            (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))
          = (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord ((infChart Γ).residue ⟨f, hf⟩) := by
    intro f hf hres E hE
    rw [filter_mem_infChart_dom_and_placeMap_eq_placeInfty_eq_filter_isInftySide Γ E,
      show (infChart Γ).placeMap = Γ.P.redFst from rfl, ← Γ.P.redFst_cuspInftyBar]
    exact Γ.supply.div_cusp f hf
      ((PlaceSpecialization.LevelOneProlongationPair.ChartFst.residue₁_ne_zero_iff Γ.R ⟨f, hf⟩).mp hres) E hE

  set H : Finset (Fin r) := Finset.univ.filter (fun l => 1 ≤ (l : ℕ)) with hHdef
  set cfun : (IsLocalRing.ResidueField ↥A) → Fin r := fun _ => l₀ with hcfun
  have hix_ex : ∀ x₀, SS.eval x₀ ≠ 0 → ∃ l : {l : Fin r // 1 ≤ (l : ℕ)}, (derivative (SS * P' l)).eval x₀ ≠ 0 :=
    fun x₀ hx => LineAlg.exists_derivative_eval_ne_zero hm P' hspan' SS hSSmonic hSSdeg hx
  set ifun : (IsLocalRing.ResidueField ↥A) → Fin r := fun x₀ => if hx : SS.eval x₀ ≠ 0 then ((hix_ex x₀ hx).choose : Fin r) else l₀ with hifun
  obtain ⟨cI, hcI⟩ := LineAlg.exists_natDegree_eq hm P' hspan'
  have hPcI0 : P' cI ≠ 0 := hli.ne_zero cI
  have hRcI : Rf (cI : Fin r) = SS * P' cI := hRf1 _ cI.2
  have hRcIdeg : (Rf (cI : Fin r)).natDegree = 2 * m - 1 := by
    rw [hRcI, natDegree_mul hSS0 hPcI0, hSSdeg, hcI]; omega
  have hRcIlc : (Rf (cI : Fin r)).leadingCoeff = (P' cI).leadingCoeff := by
    rw [hRcI, leadingCoeff_mul, hSSmonic.leadingCoeff, one_mul]

  have htop : ∀ Q : (IsLocalRing.ResidueField ↥A)[X], Q.natDegree + 1 ≤ m → (SS * Q).coeff (2 * m - 1) = Q.coeff (m - 1) := by
    intro Q hQ
    by_cases hQ' : Q.natDegree = m - 1
    · have h := coeff_mul_degree_add_degree SS Q
      rw [hSSdeg, hQ', hSSmonic.leadingCoeff, one_mul] at h
      rw [show 2 * m - 1 = m + (m - 1) by omega, h, Polynomial.leadingCoeff, hQ']
    · have hlt : Q.natDegree < m - 1 := by omega
      rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt natDegree_mul_le (by rw [hSSdeg]; omega)),
        coeff_eq_zero_of_natDegree_lt hlt]

  have hpole : ∀ l, -(((Rf (cI : Fin r)).natDegree - (1 : (IsLocalRing.ResidueField ↥A)[X]).natDegree : ℕ) : ℤ) ≤
      (cuspInftyBar (1 * p)).ord (Φ.t l) := by
    intro l
    rw [natDegree_one, Nat.sub_zero, hRcIdeg]
    by_cases h0 : Φ.t l = 0
    · rw [h0, Place.ord_zero]; omega
    · rcases (mem_riemannRochSpace_iff.mp (hmemRR l)) (cuspInftyBar (1 * p)) with h | h
      · exact (h0 h).elim
      · rw [hembApp, if_pos rfl, hembDeg] at h
        have h2 : (((2 * m - 1 : ℕ) : ℤ)) = ((2 * mAnnuli p - 1 : ℕ) : ℤ) := by rw [hmdef]
        omega

  have hcx : ∀ Q ∈ (infChart Γ).dom, ∀ x₀, (infChart Γ).placeMap Q = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      (Rf (cfun x₀)).eval x₀ ≠ 0 := by
    intro Q _ x₀ _
    show (Rf l₀).eval x₀ ≠ 0
    rw [hRfl₀, eval_one]; exact one_ne_zero

  have hix : ∀ Q ∈ (infChart Γ).dom, ∀ x₀, (infChart Γ).placeMap Q = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      (Rf (ifun x₀) * Polynomial.C ((Rf (cfun x₀)).eval x₀) - Rf (cfun x₀) * Polynomial.C ((Rf (ifun x₀)).eval x₀)).rootMultiplicity x₀ = 1 := by
    intro Q hQ x₀ hx₀
    have hx : SS.eval x₀ ≠ 0 := hSSne x₀ (hnotss Q hQ x₀ hx₀)
    have hi : ifun x₀ = ((hix_ex x₀ hx).choose : Fin r) := by simp [hifun, hx]
    have hder : (derivative (SS * P' (hix_ex x₀ hx).choose)).eval x₀ ≠ 0 := (hix_ex x₀ hx).choose_spec
    set G : (IsLocalRing.ResidueField ↥A)[X] := Rf (ifun x₀) with hGdef
    have hG : G = SS * P' (hix_ex x₀ hx).choose := by rw [hGdef, hi, hRf1 _ (hix_ex x₀ hx).choose.2]
    show (G * Polynomial.C ((Rf l₀).eval x₀) - Rf l₀ * Polynomial.C (G.eval x₀)).rootMultiplicity x₀ = 1
    rw [hRfl₀, eval_one, map_one, mul_one, one_mul]

    have hroot : (G - C (G.eval x₀)).IsRoot x₀ := by simp [IsRoot]
    have hne : G - C (G.eval x₀) ≠ 0 := by
      intro h
      have : derivative (G - C (G.eval x₀)) = 0 := by rw [h, derivative_zero]
      rw [derivative_sub, derivative_C, sub_zero] at this
      apply hder
      rw [← hG, this, eval_zero]
    have hge : 1 ≤ (G - C (G.eval x₀)).rootMultiplicity x₀ :=
      (rootMultiplicity_pos hne).mpr hroot
    have hle : ¬ 1 < (G - C (G.eval x₀)).rootMultiplicity x₀ := by
      rw [one_lt_rootMultiplicity_iff_isRoot hne]
      rintro ⟨-, h2⟩
      apply hder
      rw [← hG]
      simpa [derivative_sub, derivative_C] using h2
    omega

  have hsepx : ∀ Q ∈ (infChart Γ).dom, ∀ Q' ∈ (infChart Γ).dom, ∀ x₀ y₀,
      (infChart Γ).placeMap Q = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ → (infChart Γ).placeMap Q' = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) y₀ →
      x₀ ≠ y₀ → ∃ a b, (Rf a).eval x₀ * (Rf b).eval y₀ ≠ (Rf b).eval x₀ * (Rf a).eval y₀ := by
    intro Q hQ Q' _ x₀ y₀ hx₀ _ hxy
    have hx : SS.eval x₀ ≠ 0 := hSSne x₀ (hnotss Q hQ x₀ hx₀)
    obtain ⟨l, hl⟩ := LineAlg.exists_eval_mul_ne hm P' hspan' SS hSSmonic hSSdeg hxy hx
    refine ⟨l₀, (l : Fin r), ?_⟩
    rw [hRfl₀, hRf1 _ l.2]
    simp only [eval_one, one_mul, mul_one, eval_mul]
    exact fun h => hl h.symm

  have hHx : ∀ Q ∈ (infChart Γ).dom, ∀ x₀, (infChart Γ).placeMap Q = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      ∃ l ∈ H, (Rf l).eval x₀ ≠ 0 := by
    intro Q hQ x₀ hx₀
    have hx : SS.eval x₀ ≠ 0 := hSSne x₀ (hnotss Q hQ x₀ hx₀)
    obtain ⟨l, hl⟩ := LineAlg.exists_eval_ne_zero hm P' hspan' x₀
    refine ⟨(l : Fin r), by simp [hHdef, l.2], ?_⟩
    rw [hRf1 _ l.2, eval_mul]
    exact mul_ne_zero hx hl

  have hcInf : ∀ l, (Rf l).natDegree ≤ (Rf (cI : Fin r)).natDegree := by
    intro l
    rw [hRcIdeg]
    rcases Nat.eq_zero_or_pos (l : ℕ) with hl | hl
    · rw [hRf0 l hl, natDegree_one]; omega
    · rw [hRf1 l hl]
      have h1 := (hP l hl).1
      calc (SS * P l).natDegree ≤ SS.natDegree + (P l).natDegree := natDegree_mul_le
        _ ≤ 2 * m - 1 := by rw [hSSdeg]; omega
  have hcInfD : (1 : (IsLocalRing.ResidueField ↥A)[X]).natDegree ≤ (Rf (cI : Fin r)).natDegree := by rw [natDegree_one]; exact Nat.zero_le _
  have hcInfH : (cI : Fin r) ∈ H := by simp [hHdef, cI.2]

  have hiInf_ex : ∃ iI : Fin r,
      (Rf iI - Polynomial.C ((Rf iI).coeff (Rf (cI : Fin r)).natDegree / (Rf (cI : Fin r)).leadingCoeff) * Rf (cI : Fin r)).natDegree + 1
        = (Rf (cI : Fin r)).natDegree ∧
      Rf iI - Polynomial.C ((Rf iI).coeff (Rf (cI : Fin r)).natDegree / (Rf (cI : Fin r)).leadingCoeff) * Rf (cI : Fin r) ≠ 0 := by
    rcases Nat.lt_or_ge m 2 with hm1 | hm2
    ·
      refine ⟨l₀, ?_, ?_⟩ <;> rw [hRfl₀, hRcIdeg, coeff_one, if_neg (by omega), zero_div, map_zero, zero_mul, sub_zero]
      · rw [natDegree_one]; omega
      · exact one_ne_zero
    · obtain ⟨j, hj0, hj⟩ := LineAlg.exists_natDegree_sub_eq hm2 P' hspan' cI hcI hPcI0
      refine ⟨(j : Fin r), ?_⟩
      have hRj : Rf (j : Fin r) = SS * P' j := hRf1 _ j.2
      have hcoef : (Rf (j : Fin r)).coeff (Rf (cI : Fin r)).natDegree / (Rf (cI : Fin r)).leadingCoeff
          = (P' j).coeff (m - 1) / (P' cI).leadingCoeff := by
        rw [hRcIdeg, hRcIlc, hRj, htop _ (hP j j.2).1]
      have hfac : Rf (j : Fin r) - Polynomial.C ((Rf (j : Fin r)).coeff (Rf (cI : Fin r)).natDegree / (Rf (cI : Fin r)).leadingCoeff) * Rf (cI : Fin r)
          = SS * (P' j - C ((P' j).coeff (m - 1) / (P' cI).leadingCoeff) * P' cI) := by
        rw [hcoef, hRj, hRcI]; ring
      rw [hfac, hRcIdeg]
      refine ⟨?_, mul_ne_zero hSS0 hj0⟩
      rw [natDegree_mul hSS0 hj0, hSSdeg, hj]; omega
  obtain ⟨iI, hiInf, hiInf0⟩ := hiInf_ex

  have hsepInf : ∀ Q ∈ (infChart Γ).dom, ∀ x₀, (infChart Γ).placeMap Q = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      ∃ a b, (Rf a).eval x₀ * ((Rf b).coeff (Rf (cI : Fin r)).natDegree / (Rf (cI : Fin r)).leadingCoeff)
        ≠ (Rf b).eval x₀ * ((Rf a).coeff (Rf (cI : Fin r)).natDegree / (Rf (cI : Fin r)).leadingCoeff) := by
    intro Q _ x₀ _
    refine ⟨l₀, (cI : Fin r), ?_⟩
    have hlc : (Rf (cI : Fin r)).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by rw [hRcI]; exact mul_ne_zero hSS0 hPcI0)
    rw [hRfl₀, eval_one, one_mul, coeff_one, hRcIdeg, if_neg (by omega), zero_div, mul_zero,
      ← hRcIdeg, coeff_natDegree, div_self hlc]
    exact one_ne_zero

  obtain ⟨cQ, iQ, h1, h2, h3, h4, h5, h6, h7⟩ :=
    ModularCurve.exists_chartData_of_lineResidues hFrat (infChart Γ) Φ.t hint hunit 1 Rf one_ne_zero hR
      (cuspInftyBar (1 * p)) hc₀ hc₀inf hreg₀ hdom hcusp cfun ifun H hcx hix hsepx hHx (cI : Fin r) iI
      hcInf hcInfD hcInfH hpole hiInf hiInf0 hsepInf
  refine ⟨hint, cQ, iQ, h1, h2, h3, h4, h5, h6, fun μ hμ Q hQ => ?_⟩
  obtain ⟨l, hl, h⟩ := h7 μ hμ Q hQ
  exact ⟨l, (Finset.mem_filter.mp hl).2, h⟩

end S_ModularCurve_MultCovering_infChart_chartData_goodFamily
end P2MW
export P2MW.S_ModularCurve_MultCovering_infChart_chartData_goodFamily (solution)

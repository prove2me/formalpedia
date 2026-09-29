-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_residue_eq_of_regular_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/95fa6ad5-cc47-511f-82a9-f8ebc5560e43

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_ModularCurve_exists_linearIndependent_residuePair_of_finiteDimensional
import Theorems.Thm_ModularCurve_finiteDimensional_riemannRochSpace_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_degree_add_one_sub_genusFF_le_finrank_riemannRochSpace_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_LevelOneFibre_genusFF_lt_card_of_ssJSet
import Theorems.Thm_AlgebraicCurve_finrank_nodeCompatible_add_min_card_le_of_ringEquiv_ratFunc
import Theorems.Thm_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc
import Theorems.Thm_ModularCurve_linearIndependent_map_prod_of_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residuePair_mem_riemannRochSpace_of_isGoodDivisor
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_basis_riemannRochSpace_coeffMap_eq_smul_of_isGoodDivisor
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_riemannRochSpace_residue_eq_of_regular_of_nonneg
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace FltWs24
namespace Asm

section NodePairs

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_zero' (v : Place K F) : v.HasValue (0 : F) 0 := by
  simpa using Place.hasValue_algebraMap v (0 : K)

theorem hasValue_add' {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_smul' {v : Place K F} {g : F} {a : K} (c : K) (h : v.HasValue g a) :
    v.HasValue (c • g) (c * a) := by
  rw [Algebra.smul_def]
  exact (Place.hasValue_algebraMap v c).mul h

def nodeCompatiblePairs (E₁ E₂ : Divisor K F) {ι : Type*} (v₁ v₂ : ι → Place K F) :
    Submodule K (F × F) where
  carrier := {p | p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
    ∀ i, ∃ c : K, (v₁ i).HasValue p.1 c ∧ (v₂ i).HasValue p.2 c}
  zero_mem' := ⟨Submodule.zero_mem _, Submodule.zero_mem _,
    fun i => ⟨0, hasValue_zero' _, hasValue_zero' _⟩⟩
  add_mem' := by
    rintro p p' ⟨hp1, hp2, hp⟩ ⟨hq1, hq2, hq⟩
    refine ⟨Submodule.add_mem _ hp1 hq1, Submodule.add_mem _ hp2 hq2, fun i => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := hp i
    obtain ⟨d, hd1, hd2⟩ := hq i
    exact ⟨c + d, hasValue_add' hc1 hd1, hasValue_add' hc2 hd2⟩
  smul_mem' := by
    rintro a p ⟨hp1, hp2, hp⟩
    refine ⟨Submodule.smul_mem _ a hp1, Submodule.smul_mem _ a hp2, fun i => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := hp i
    exact ⟨a * c, hasValue_smul' a hc1, hasValue_smul' a hc2⟩

theorem mem_nodeCompatiblePairs_iff {E₁ E₂ : Divisor K F} {ι : Type*} {v₁ v₂ : ι → Place K F}
    {p : F × F} :
    p ∈ nodeCompatiblePairs E₁ E₂ v₁ v₂ ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : K, (v₁ i).HasValue p.1 c ∧ (v₂ i).HasValue p.2 c :=
  Iff.rfl

end NodePairs

section Descent

theorem mem_span_of_map_mem {k₀ k : Type*} [Field k₀] [Field k] (σ : k₀ →+* k)
    (F₀ : IntermediateField k₀ (LaurentSeries k₀)) (F : IntermediateField k (LaurentSeries k))
    (ι : F₀ →+* F) (hι : ∀ x : F₀, ((ι x : F) : LaurentSeries k) = coeffMap σ (x : LaurentSeries k₀))
    {n : ℕ} (r : Fin n → F₀ × F₀) (hr : LinearIndependent k₀ r)
    (T : Submodule k (F × F)) [FiniteDimensional k T]
    (hT : ∀ j, ((ι (r j).1 : F), (ι (r j).2 : F)) ∈ T) (hTn : Module.finrank k T ≤ n)
    (g : F₀ × F₀) (hg : ((ι g.1 : F), (ι g.2 : F)) ∈ T) :
    g ∈ Submodule.span k₀ (Set.range r) := by
  let φ : F₀ × F₀ → F × F := fun y => ((ι y.1 : F), (ι y.2 : F))
  have hpli : LinearIndependent k (φ ∘ r) := linearIndependent_map_prod_of_coe_eq_coeffMap σ F₀ F ι hι hr
  have hspan : Submodule.span k (Set.range (φ ∘ r)) = T := by
    refine Submodule.eq_of_le_of_finrank_le (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨j, rfl⟩
      exact hT j
    · rw [finrank_span_eq_card hpli, Fintype.card_fin]
      exact hTn
  by_contra hnot
  have hli' : LinearIndependent k₀ (Fin.cons g r) := by
    first
      | exact linearIndependent_finCons.mpr ⟨hr, hnot⟩
      | exact linearIndependent_fin_cons.mpr ⟨hr, hnot⟩
  have himg : LinearIndependent k (φ ∘ Fin.cons g r) :=
    linearIndependent_map_prod_of_coe_eq_coeffMap σ F₀ F ι hι hli'
  rw [Fin.comp_cons] at himg
  first
    | (rw [linearIndependent_finCons, hspan] at himg; exact himg.2 hg)
    | (rw [linearIndependent_fin_cons, hspan] at himg; exact himg.2 hg)

end Descent

section Degrees

variable {K F K' F' : Type*} [Field K] [Field F] [Algebra K F] [Field K'] [Field F'] [Algebra K' F']

theorem degree_mapDomain_of_deg_eq_one (r : Place K F → Place K' F')
    (h1 : ∀ w : Place K F, w.deg = 1) (h1' : ∀ v : Place K' F', v.deg = 1) (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain r D) = Divisor.degree D := by
  classical
  simp only [Divisor.degree, Finsupp.liftAddHom_apply]
  rw [Finsupp.sum_mapDomain_index]
  · refine Finsupp.sum_congr fun w _ => ?_
    show D w * ((r w).deg : ℤ) = D w * (w.deg : ℤ)
    rw [h1, h1']
  · intro v; exact zero_mul _
  · intro v m n; exact add_mul _ _ _

theorem degree_nonneg_of_deg_eq_one (h1 : ∀ w : Place K F, w.deg = 1) {D : Divisor K F} (hD : ∀ w, 0 ≤ D w) :
    0 ≤ Divisor.degree D := by
  simp only [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finset.sum_nonneg fun w _ => ?_
  show 0 ≤ D w * (w.deg : ℤ)
  rw [h1]; simpa using hD w

end Degrees

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem frob_frob_charLGeomPlaceOfPoint {a : k} (ha : a ^ (q ^ 2) = a) :
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a))
      = charLGeomPlaceOfPoint k a := by
  haveI : PerfectField k := inferInstance
  rw [← arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr (charLGeomPlaceOfPoint k a),
    arithFrobC_smul_charLGeomPlaceOfPoint q a,
    ← arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr (charLGeomPlaceOfPoint k (a ^ q)),
    arithFrobC_smul_charLGeomPlaceOfPoint q (a ^ q), ← pow_mul, ← sq, ha]

theorem pow_q_pow_q_sq_eq {a : k} (ha : a ^ (q ^ 2) = a) : (a ^ q) ^ (q ^ 2) = a ^ q := by
  rw [← pow_mul, mul_comm, pow_mul, ha]

theorem mapDomain_redFst_fstPart_eq_zero (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    {v : Place k (modularFunctionFieldC k 1)}
    (hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v) :
    Finsupp.mapDomain P.redFst (P.fstPart D) v = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun W hW => ?_
  rw [Finsupp.single_apply, if_neg]
  intro hWv

  have hW' : W ∈ (P.fstPart D).support := hW
  unfold PlaceSpecialization.fstPart at hW'
  rw [Finsupp.support_filter, Finset.mem_filter] at hW'
  have h1 : P.IsStrictTypeOne W := hW'.2
  exact h1.2 (hWv ▸ hv)

theorem mapDomain_redSnd_sndPart_eq_zero (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    {v : Place k (modularFunctionFieldC k 1)}
    (hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v) :
    Finsupp.mapDomain P.redSnd (P.sndPart D) v = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun W hW => ?_
  rw [Finsupp.single_apply, if_neg]
  intro hWv
  have hW' : W ∈ (P.sndPart D).support := hW
  unfold PlaceSpecialization.sndPart at hW'
  rw [Finsupp.support_filter, Finset.mem_filter] at hW'
  have h1 : P.IsStrictTypeTwo W := hW'.2
  exact h1.2 (hWv ▸ hv)

end FltWs24.Asm

namespace FltWs24
namespace Asm

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

set_option maxHeartbeats 6400000 in

theorem count (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hD : ∀ W, 0 ≤ D W) (hgood : P.IsGoodDivisor D)
    (hdeg : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) : ℤ) ≤ D.degree + 1) :
    FiniteDimensional k (nodeCompatiblePairs (Finsupp.mapDomain P.redFst (P.fstPart D)) (Finsupp.mapDomain P.redSnd (P.sndPart D))
      (fun s : ↥S₀ => (frobNodePair q (s : k)).1) (fun s : ↥S₀ => (frobNodePair q (s : k)).2)) ∧
    Module.finrank k (nodeCompatiblePairs (Finsupp.mapDomain P.redFst (P.fstPart D)) (Finsupp.mapDomain P.redSnd (P.sndPart D))
      (fun s : ↥S₀ => (frobNodePair q (s : k)).1) (fun s : ↥S₀ => (frobNodePair q (s : k)).2)) ≤ Module.finrank (AlgebraicClosure ℚ) (riemannRochSpace D) := by
  classical
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  have hRR := degree_add_one_sub_genusFF_le_finrank_riemannRochSpace_modularFunctionFieldBar D
  set T : Submodule k (modularFunctionFieldC k 1 × modularFunctionFieldC k 1) := nodeCompatiblePairs (Finsupp.mapDomain P.redFst (P.fstPart D)) (Finsupp.mapDomain P.redSnd (P.sndPart D))
      (fun s : ↥S₀ => (frobNodePair q (s : k)).1) (fun s : ↥S₀ => (frobNodePair q (s : k)).2) with hT
  have hdegBar : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), w.deg = 1 :=
    deg_eq_one_modularFunctionFieldBar (1 * q)
  have hdegC : ∀ v : Place k (modularFunctionFieldC k 1), v.deg = 1 := place_deg_eq_one_of_isAlgClosed k 1
  have hD₁nn : ∀ W, 0 ≤ P.fstPart D W := fun W => by
    unfold PlaceSpecialization.fstPart; rw [Finsupp.filter_apply]; split_ifs; exact hD W; exact le_rfl
  have hD₂nn : ∀ W, 0 ≤ P.sndPart D W := fun W => by
    unfold PlaceSpecialization.sndPart; rw [Finsupp.filter_apply]; split_ifs; exact hD W; exact le_rfl
  have hE₁ : (0 : Divisor k (modularFunctionFieldC k 1)) ≤ Finsupp.mapDomain P.redFst (P.fstPart D) := by
    have h : (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ≤ P.fstPart D := fun W => by simpa using hD₁nn W
    simpa using Finsupp.mapDomain_mono (f := P.redFst) h
  have hE₂ : (0 : Divisor k (modularFunctionFieldC k 1)) ≤ Finsupp.mapDomain P.redSnd (P.sndPart D) := by
    have h : (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ≤ P.sndPart D := fun W => by simpa using hD₂nn W
    simpa using Finsupp.mapDomain_mono (f := P.redSnd) h

  have hd₁ : Divisor.degree (Finsupp.mapDomain P.redFst (P.fstPart D)) = Divisor.degree (P.fstPart D) :=
    degree_mapDomain_of_deg_eq_one _ hdegBar hdegC _
  have hd₂ : Divisor.degree (Finsupp.mapDomain P.redSnd (P.sndPart D)) = Divisor.degree (P.sndPart D) :=
    degree_mapDomain_of_deg_eq_one _ hdegBar hdegC _
  have hparts : P.fstPart D + P.sndPart D = D := by
    ext W
    unfold PlaceSpecialization.fstPart PlaceSpecialization.sndPart
    rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases h1 : P.IsStrictTypeOne W
    · by_cases h2 : P.IsStrictTypeTwo W
      · exact absurd (by rw [h1.1]; exact h2.1.symm) h1.2
      · rw [if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : P.IsStrictTypeTwo W
      · rw [if_neg h1, if_pos h2, zero_add]
      · rw [if_neg h1, if_neg h2, add_zero]
        by_contra h
        rcases hgood W (Finsupp.mem_support_iff.mpr (Ne.symm h)) with h' | h'
        · exact h1 h'
        · exact h2 h'
  have hsum : Divisor.degree (P.fstPart D) + Divisor.degree (P.sndPart D) = Divisor.degree D := by
    rw [← map_add, hparts]
  have hd₁nn : 0 ≤ Divisor.degree (P.fstPart D) := degree_nonneg_of_deg_eq_one hdegBar hD₁nn
  have hd₂nn : 0 ≤ Divisor.degree (P.sndPart D) := degree_nonneg_of_deg_eq_one hdegBar hD₂nn

  have hfrob : Function.Injective (fun a : k => a ^ q) := fun a b h => by
    have h' : a ^ q = b ^ q := h
    have : (a - b) ^ q = 0 := by rw [sub_pow_char, h', sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : q.Prime).ne_zero |>.mp this)
  have hP1 := AlgebraicCurve.finrank_nodeCompatible_add_min_card_le_of_ringEquiv_ratFunc
    (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
    (Finsupp.mapDomain P.redFst (P.fstPart D)) (Finsupp.mapDomain P.redSnd (P.sndPart D)) hE₁ hE₂
    (fun s : ↥S₀ => (s : k)) (fun s : ↥S₀ => (s : k) ^ q)
    Subtype.val_injective (hfrob.comp Subtype.val_injective)
    (fun s => mapDomain_redFst_fstPart_eq_zero P D
      (frob_frob_charLGeomPlaceOfPoint (pow_q_sq_eq_self_of_mem_ssJSet q ((hS₀ s).mp s.2))))
    (fun s => mapDomain_redSnd_sndPart_eq_zero P D
      (frob_frob_charLGeomPlaceOfPoint (pow_q_pow_q_sq_eq (pow_q_sq_eq_self_of_mem_ssJSet q ((hS₀ s).mp s.2)))))
    T (fun x => Iff.rfl)
  have hcard : genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) < S₀.card := LevelOneFibre.genusFF_lt_card_of_ssJSet S₀ hS₀
  have hRR := degree_add_one_sub_genusFF_le_finrank_riemannRochSpace_modularFunctionFieldBar D
  rw [Fintype.card_coe, hd₁, hd₂] at hP1
  have hTn : Module.finrank k T ≤ Module.finrank (AlgebraicClosure ℚ) (riemannRochSpace D) := by

    omega

  have hfinT : FiniteDimensional k T := by
    have h1 := AlgebraicCurve.finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc
      (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c) _ hE₁
    have h2 := AlgebraicCurve.finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc
      (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c) _ hE₂
    haveI : FiniteDimensional k (riemannRochSpace (Finsupp.mapDomain P.redFst (P.fstPart D))) :=
      Module.finite_of_finrank_pos (by omega)
    haveI : FiniteDimensional k (riemannRochSpace (Finsupp.mapDomain P.redSnd (P.sndPart D))) :=
      Module.finite_of_finrank_pos (by omega)
    let f : T →ₗ[k] (riemannRochSpace (Finsupp.mapDomain P.redFst (P.fstPart D))) ×
        (riemannRochSpace (Finsupp.mapDomain P.redSnd (P.sndPart D))) :=
      { toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2.1⟩)
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl }
    exact Module.Finite.of_injective f (fun x y h => by
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z => ((z.1 : riemannRochSpace (Finsupp.mapDomain P.redFst (P.fstPart D))) :
          modularFunctionFieldC k 1)) h
      · exact congrArg (fun z => ((z.2 : riemannRochSpace (Finsupp.mapDomain P.redSnd (P.sndPart D))) :
          modularFunctionFieldC k 1)) h)
  exact ⟨hfinT, hTn⟩

set_option maxHeartbeats 6400000 in
theorem main {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hval : LevelOneProlongationPair.NodeValueLaw q red)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) (hNR : R.RegularityLaw S₀)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hD : ∀ W, 0 ≤ D W) (hgood : P.IsGoodDivisor D)
    (hdeg : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) : ℤ) ≤ D.degree + 1)
    (g₁ g₂ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)
    (hg₁ : (R.ι g₁ : modularFunctionFieldC k 1) ∈
      riemannRochSpace (Finsupp.mapDomain P.redFst (P.fstPart D)))
    (hg₂ : (R.ι g₂ : modularFunctionFieldC k 1) ∈
      riemannRochSpace (Finsupp.mapDomain P.redSnd (P.sndPart D)))
    (hnode : ∀ a ∈ S₀, ∃ c : k,
      (frobNodePair q a).1.HasValue (R.ι g₁ : modularFunctionFieldC k 1) c ∧
      (frobNodePair q a).2.HasValue (R.ι g₂ : modularFunctionFieldC k 1) c) :
    ∃ (G : modularFunctionFieldBar (1 * q)) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      G ∈ riemannRochSpace D ∧ R.R₁.residue ⟨G, h₁⟩ = g₁ ∧ R.R₂.residue ⟨G, h₂⟩ = g₂ := by
  classical
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  haveI hfd : FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace D) :=
    finiteDimensional_riemannRochSpace_modularFunctionFieldBar D
  have hRR := degree_add_one_sub_genusFF_le_finrank_riemannRochSpace_modularFunctionFieldBar D

  obtain ⟨hfinT, hTn⟩ := count P S₀ hS₀ D hD hgood hdeg

  obtain ⟨b, hbV, hbli, hbint⟩ :=
    PlaceSpecialization.exists_basis_riemannRochSpace_coeffMap_eq_smul_of_isGoodDivisor P D hgood
  obtain ⟨Gf, hG₁, hG₂, hGV, hGli⟩ :=
    exists_linearIndependent_residuePair_of_finiteDimensional R.R₁ R.R₂ R.residue₁_coeffMap
      R.mem_integers₂_iff R.residue₂_eq (riemannRochSpace D) ⟨b, hbV, hbli, hbint⟩

  set r := fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩) with hr
  set φ : modularFunctionFieldFullC (ResidueField A) 1 × modularFunctionFieldFullC (ResidueField A) 1 →
      modularFunctionFieldC k 1 × modularFunctionFieldC k 1 := fun y => (R.ι y.1, R.ι y.2) with hφ

  set T : Submodule k (modularFunctionFieldC k 1 × modularFunctionFieldC k 1) :=
    nodeCompatiblePairs (Finsupp.mapDomain P.redFst (P.fstPart D)) (Finsupp.mapDomain P.redSnd (P.sndPart D))
      (fun s : ↥S₀ => (frobNodePair q (s : k)).1) (fun s : ↥S₀ => (frobNodePair q (s : k)).2) with hT
  have hpT : ∀ j, (φ ∘ r) j ∈ T := fun j => by
    obtain ⟨h1, h2, h3⟩ :=
      LevelOneProlongationPair.residuePair_mem_riemannRochSpace_of_isGoodDivisor R hR S₀ hS₀ hNR D hD hgood
        (Gf j) (hGV j) (hG₁ j) (hG₂ j)
    exact ⟨h1, h2, fun s => h3 s s.2⟩
  have hgT : φ (g₁, g₂) ∈ T := ⟨hg₁, hg₂, fun s => hnode s s.2⟩

  haveI := hfinT
  have hgspan : (g₁, g₂) ∈ Submodule.span (ResidueField A) (Set.range r) :=
    mem_span_of_map_mem R.redBar _ _ R.ι R.ι_coe r hGli T hpT hTn (g₁, g₂) hgT
  obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun (ResidueField A)).mp hgspan

  choose α hα using fun j => IsLocalRing.residue_surjective (μ j)
  have hcmem₁ : ∀ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (α j : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
    fun j => (R.R₁.algebraMap_mem_iff _).mpr (α j).2
  have hcmem₂ : ∀ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (α j : AlgebraicClosure ℚ) ∈ R.R₂.integers :=
    fun j => (R.R₂.algebraMap_mem_iff _).mpr (α j).2
  set cs₁ : _ → R.R₁.integers := fun j => ⟨_, hcmem₁ j⟩ with hcs₁
  set Gs₁ : _ → R.R₁.integers := fun j => ⟨Gf j, hG₁ j⟩ with hGs₁
  set cs₂ : _ → R.R₂.integers := fun j => ⟨_, hcmem₂ j⟩ with hcs₂
  set Gs₂ : _ → R.R₂.integers := fun j => ⟨Gf j, hG₂ j⟩ with hGs₂
  set x₁ : R.R₁.integers := ∑ j, cs₁ j * Gs₁ j with hx₁
  set x₂ : R.R₂.integers := ∑ j, cs₂ j * Gs₂ j with hx₂
  set G : modularFunctionFieldBar (1 * q) :=
    ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (α j : AlgebraicClosure ℚ) * Gf j with hGdef
  have hsum₁ : (x₁ : modularFunctionFieldBar (1 * q)) = G := by
    have e : ((∑ j, cs₁ j * Gs₁ j : R.R₁.integers) : modularFunctionFieldBar (1 * q))
        = ∑ j, ((cs₁ j * Gs₁ j : R.R₁.integers) : modularFunctionFieldBar (1 * q)) := by
      first
        | exact AddSubmonoidClass.coe_finsetSum _ _
        | exact AddSubmonoidClass.coe_finset_sum _ _
    rw [hx₁, e, hGdef]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MulMemClass.coe_mul]
    try rfl
  have hsum₂ : (x₂ : modularFunctionFieldBar (1 * q)) = G := by
    have e : ((∑ j, cs₂ j * Gs₂ j : R.R₂.integers) : modularFunctionFieldBar (1 * q))
        = ∑ j, ((cs₂ j * Gs₂ j : R.R₂.integers) : modularFunctionFieldBar (1 * q)) := by
      first
        | exact AddSubmonoidClass.coe_finsetSum _ _
        | exact AddSubmonoidClass.coe_finset_sum _ _
    rw [hx₂, e, hGdef]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MulMemClass.coe_mul]
    try rfl

  have hterm₁ : ∀ j, R.R₁.residue (cs₁ j * Gs₁ j) = μ j • (r j).1 := by
    intro j
    have hc : R.R₁.residue (cs₁ j) = algebraMap (ResidueField A) _ (μ j) := by
      rw [← hα j]
      exact R.R₁.residue_algebraMap (α j)
    rw [map_mul, Algebra.smul_def]
    exact congrArg (· * _) hc
  have hterm₂ : ∀ j, R.R₂.residue (cs₂ j * Gs₂ j) = μ j • (r j).2 := by
    intro j
    have hc : R.R₂.residue (cs₂ j) = algebraMap (ResidueField A) _ (μ j) := by
      rw [← hα j]
      exact R.R₂.residue_algebraMap (α j)
    rw [map_mul, Algebra.smul_def]
    exact congrArg (· * _) hc

  have h₁ : G ∈ R.R₁.integers := by
    rw [← hsum₁]
    exact x₁.2
  have h₂ : G ∈ R.R₂.integers := by
    rw [← hsum₂]
    exact x₂.2
  have hGx₁ : (⟨G, h₁⟩ : R.R₁.integers) = x₁ := by
    apply Subtype.ext
    exact hsum₁.symm
  have hGx₂ : (⟨G, h₂⟩ : R.R₂.integers) = x₂ := by
    apply Subtype.ext
    exact hsum₂.symm
  refine ⟨G, h₁, h₂, ?_, ?_, ?_⟩
  · rw [hGdef]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hGV j)
  · rw [hGx₁, hx₁, map_sum, Finset.sum_congr rfl fun j _ => hterm₁ j]
    have h1 := congrArg Prod.fst hμ
    rw [Prod.fst_sum] at h1
    simpa only [Prod.smul_fst] using h1
  · rw [hGx₂, hx₂, map_sum, Finset.sum_congr rfl fun j _ => hterm₂ j]
    have h1 := congrArg Prod.snd hμ
    rw [Prod.snd_sum] at h1
    simpa only [Prod.smul_snd] using h1

end FltWs24.Asm

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hval : LevelOneProlongationPair.NodeValueLaw q red)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) (hNR : R.RegularityLaw S₀)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hD : ∀ W, 0 ≤ D W) (hgood : P.IsGoodDivisor D)
    (hdeg : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) : ℤ) ≤ D.degree + 1)
    (g₁ g₂ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)
    (hg₁ : (R.ι g₁ : modularFunctionFieldC k 1) ∈
      riemannRochSpace (Finsupp.mapDomain P.redFst (P.fstPart D)))
    (hg₂ : (R.ι g₂ : modularFunctionFieldC k 1) ∈
      riemannRochSpace (Finsupp.mapDomain P.redSnd (P.sndPart D)))
    (hnode : ∀ a ∈ S₀, ∃ c : k,
      (frobNodePair q a).1.HasValue (R.ι g₁ : modularFunctionFieldC k 1) c ∧
      (frobNodePair q a).2.HasValue (R.ι g₂ : modularFunctionFieldC k 1) c) :
    ∃ (G : modularFunctionFieldBar (1 * q)) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      G ∈ riemannRochSpace D ∧ R.R₁.residue ⟨G, h₁⟩ = g₁ ∧ R.R₂.residue ⟨G, h₂⟩ = g₂ :=
  FltWs24.Asm.main R hR hO hval S₀ hS₀ hNR D hD hgood hdeg g₁ g₂ hg₁ hg₂ hnode

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_riemannRochSpace_residue_eq_of_regular_of_nonneg
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_riemannRochSpace_residue_eq_of_regular_of_nonneg (solution)

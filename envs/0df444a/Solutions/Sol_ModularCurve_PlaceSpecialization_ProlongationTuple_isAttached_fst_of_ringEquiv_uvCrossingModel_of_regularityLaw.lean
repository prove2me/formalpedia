-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.isAttached_fst_of_ringEquiv_uvCrossingModel_of_regularityLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c3126612-f33b-5a93-b75b-1d16322b3758

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_zpow
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_ModularCurve_PlaceSpecialization_not_fixed_reduceFst_of_isStrictSnd
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_nodeResidue_nonneg_of_regularityLaw
import Theorems.Thm_AlgebraicCurve_Place_hasValue_iff_mem_and_eq_or_ord_sub_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isAttached_fst_of_ringEquiv_uvCrossingModel_of_regularityLaw
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace Ws34
namespace EndAttach

theorem frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_and_isAffineGeomPlace_of_mem_ssPlaces
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data) (hqN : ¬ q ∣ N)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) :
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w ∧ IsAffineGeomPlace k N w := by
  refine ⟨?_, hw.2.1⟩
  have h2 := ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q N hqN k w hw
  rwa [ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w,
    ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr] at h2

theorem not_isStrictFst_and_not_isStrictSnd_of_reduceFst_eq_of_mem_ssPlaces
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := by
  have hfix := (frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_and_isAffineGeomPlace_of_mem_ssPlaces
    data hKr hqN w hw).1
  rw [← hV] at hfix
  exact ⟨fun h => h.2 hfix, fun h => ModularCurve.PlaceSpecialization.not_fixed_reduceFst_of_isStrictSnd P V h hfix⟩

theorem mem_dom_iff_reduceFst_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    {dom : Set (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))}
    (hdom : ∀ V', V' ∈ dom ↔ (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    V ∈ dom ↔ P.reduceFst V = w := by
  rw [hdom V]
  exact ⟨fun h => h.1, fun h => ⟨h, not_isStrictFst_and_not_isStrictSnd_of_reduceFst_eq_of_mem_ssPlaces P hqN w hw V h⟩⟩

section Eval

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

theorem isUnit_mk_of_ord_eq_zero (V : Place L F) {z : F} (hz : z ∈ V.toValuationSubring) (hz0 : z ≠ 0)
    (hord : V.ord z = 0) : IsUnit (⟨z, hz⟩ : V.toValuationSubring) := by
  rw [← V.adicValuation_coe_eq_one_iff]
  change V.adicValuation z = 1
  have hne : V.adicValuation z ≠ 0 := V.adicValuation_ne_zero hz0
  have hlog : WithZero.log (V.adicValuation z) = 0 := by
    have : -(WithZero.log (V.adicValuation z)) = 0 := hord
    omega
  rw [← WithZero.exp_log hne, hlog, WithZero.exp_zero]

theorem inv_mem_of_ord_eq_zero (V : Place L F) {z : F} (hz : z ∈ V.toValuationSubring) (hz0 : z ≠ 0)
    (hord : V.ord z = 0) : z⁻¹ ∈ V.toValuationSubring := by
  obtain ⟨b, hb⟩ := (isUnit_mk_of_ord_eq_zero V hz hz0 hord).exists_right_inv
  have hb' : z * (b : F) = 1 := by simpa using congrArg Subtype.val hb
  rw [inv_eq_of_mul_eq_one_right hb']
  exact b.2

theorem zpow_mem_of_ord_eq_zero (V : Place L F) {z : F} (hz : z ∈ V.toValuationSubring) (hz0 : z ≠ 0)
    (hord : V.ord z = 0) (m : ℤ) : z ^ m ∈ V.toValuationSubring := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [zpow_natCast]; exact pow_mem hz n
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_mem (inv_mem_of_ord_eq_zero V hz hz0 hord) n

theorem evalAt_mul_zpow_neg (V : Place L F) (hV : V.IsRational) {f z : F} (hf : f ∈ V.toValuationSubring)
    (hz : z ∈ V.toValuationSubring) (hz0 : z ≠ 0) (hord : V.ord z = 0) (n : ℤ) :
    V.evalAt (f * z ^ (-n)) = V.evalAt f * V.evalAt z ^ (-n) := by
  rw [V.evalAt_mul hV hf (zpow_mem_of_ord_eq_zero V hz hz0 hord (-n)), V.evalAt_zpow hV hz0 hord]

theorem ord_eq_zero_of_evalAt_ne_zero (V : Place L F) {z : F} (hz : z ∈ V.toValuationSubring)
    (h : V.evalAt z ≠ 0) : V.ord z = 0 := by
  by_contra hne
  apply h
  have hnu : ¬ IsUnit (⟨z, hz⟩ : V.toValuationSubring) := by
    intro hu
    exact hne (by simpa using V.ord_coe_unit hu.unit)
  have hmem : (⟨z, hz⟩ : V.toValuationSubring) ∈ maximalIdeal V.toValuationSubring := hnu
  rw [V.evalAt_of_mem hz, (IsLocalRing.residue_eq_zero_iff _).mpr hmem, ← map_zero (algebraMap L V.ResidueField),
    V.residueInv_algebraMap]

theorem isUnit_mk_evalAt_of_inv (A : ValuationSubring L) (V : Place L F) (hV : V.IsRational) {g : F} (hg0 : g ≠ 0)
    (hg : g ∈ V.toValuationSubring) (hg' : g⁻¹ ∈ V.toValuationSubring)
    (hA : V.evalAt g ∈ A) (hA' : V.evalAt g⁻¹ ∈ A) : IsUnit (⟨V.evalAt g, hA⟩ : A) := by
  refine isUnit_iff_exists_inv.mpr ⟨⟨V.evalAt g⁻¹, hA'⟩, Subtype.ext ?_⟩
  change V.evalAt g * V.evalAt g⁻¹ = 1
  rw [← V.evalAt_mul hV hg hg', mul_inv_cancel₀ hg0, V.evalAt_one]

end Eval

section UnitZpow

variable {F E : Type*} [Field F] [Field E] (S : ValuationSubring F)

theorem isUnit_mk_iff_inv_mem {s : F} (hs : s ∈ S) (hs0 : s ≠ 0) :
    IsUnit (⟨s, hs⟩ : S) ↔ s⁻¹ ∈ S := by
  constructor
  · intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : s * (b : F) = 1 := by simpa using congrArg Subtype.val hb
    rw [inv_eq_of_mul_eq_one_right hb']
    exact b.2
  · intro hinv
    exact isUnit_iff_exists_inv.mpr ⟨⟨s⁻¹, hinv⟩, Subtype.ext (by simpa using mul_inv_cancel₀ hs0)⟩

theorem ne_zero_of_isUnit_mk {s : F} (hs : s ∈ S) (hu : IsUnit (⟨s, hs⟩ : S)) : s ≠ 0 := by
  rintro rfl
  rw [show (⟨(0 : F), hs⟩ : S) = 0 from rfl] at hu
  exact not_isUnit_zero hu

theorem inv_mem_of_isUnit_mk {s : F} (hs : s ∈ S) (hu : IsUnit (⟨s, hs⟩ : S)) : s⁻¹ ∈ S :=
  (isUnit_mk_iff_inv_mem S hs (ne_zero_of_isUnit_mk S hs hu)).mp hu

theorem zpow_mem_of_isUnit_mk {s : F} (hs : s ∈ S) (hu : IsUnit (⟨s, hs⟩ : S)) (m : ℤ) : s ^ m ∈ S := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [zpow_natCast]; exact pow_mem hs n
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_mem (inv_mem_of_isUnit_mk S hs hu) n

theorem map_mk_inv {s : F} (hs : s ∈ S) (hu : IsUnit (⟨s, hs⟩ : S)) (φ : S →+* E) :
    φ ⟨s⁻¹, inv_mem_of_isUnit_mk S hs hu⟩ = (φ ⟨s, hs⟩)⁻¹ := by
  have hs0 := ne_zero_of_isUnit_mk S hs hu
  have hmul : (⟨s, hs⟩ : S) * ⟨s⁻¹, inv_mem_of_isUnit_mk S hs hu⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hs0)
  have h := congrArg φ hmul
  rw [map_mul, map_one] at h
  exact (inv_eq_of_mul_eq_one_right h).symm

theorem map_mk_zpow {s : F} (hs : s ∈ S) (hu : IsUnit (⟨s, hs⟩ : S)) (m : ℤ) (φ : S →+* E) :
    φ ⟨s ^ m, zpow_mem_of_isUnit_mk S hs hu m⟩ = (φ ⟨s, hs⟩) ^ m := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have : (⟨s ^ (n : ℤ), zpow_mem_of_isUnit_mk S hs hu n⟩ : S) = ⟨s, hs⟩ ^ n :=
      Subtype.ext (by simp)
    rw [this, map_pow, zpow_natCast]
  · have : (⟨s ^ (-(n : ℤ)), zpow_mem_of_isUnit_mk S hs hu (-(n : ℤ))⟩ : S) =
        (⟨s⁻¹, inv_mem_of_isUnit_mk S hs hu⟩ : S) ^ n :=
      Subtype.ext (by simp)
    rw [this, map_pow, map_mk_inv S hs hu φ, inv_pow, zpow_neg, zpow_natCast]

theorem inv_mem_and_map_mk_inv {s : F} (hs : s ∈ S) (hu : IsUnit (⟨s, hs⟩ : S)) :
    ∃ h : s⁻¹ ∈ S, ∀ φ : S →+* E, φ ⟨s⁻¹, h⟩ = (φ ⟨s, hs⟩)⁻¹ :=
  ⟨inv_mem_of_isUnit_mk S hs hu, fun φ => map_mk_inv S hs hu φ⟩

end UnitZpow

section Constants

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

private theorem _root_.Ws34.EndAttach.evalAt_algebraMap (V : Place L F) (a : L) : V.evalAt (algebraMap L F a) = a :=
  V.evalAt_algebraMap a

p2m_export "Ws34.EndAttach" "evalAt_algebraMap"

private theorem _root_.Ws34.EndAttach.ord_algebraMap (V : Place L F) {a : L} (ha : a ≠ 0) : V.ord (algebraMap L F a) = 0 :=
  AlgebraicCurve.ConstantReduction.ord_algebraMap V ha

p2m_export "Ws34.EndAttach" "ord_algebraMap"
end Constants

end Ws34.EndAttach

namespace Ws34
namespace EndAttachFst

open Ws34.EndAttach

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

variable (R : ProlongationTuple P)

theorem ord_residue₁_pos_of_residue₂_eq_zero [IsAlgClosed k] [DecidableEq k]
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) {w : Place k (modularFunctionFieldC k N)} (hwW₀ : w ∈ W₀)
    (hreg : R.RegularityLaw W₀)
    (g : ↥(modularFunctionFieldBar (N * q))) (h₂ : g ∈ R.R₂.integers) (h₁ : g ∈ R.R₁.integers)
    (hpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → 0 ≤ V.ord g)
    (h0 : R.residue₂ ⟨g, h₂⟩ = 0) (hne : R.residue₁ ⟨g, h₁⟩ ≠ 0) :
    0 < w.ord (R.residue₁ ⟨g, h₁⟩) := by
  obtain ⟨cv, hv₁, hv₂⟩ := hreg.2 g h₁ h₂ (smulNodePair (arithFrobC q k N) w)
    (smulNodePair_mem_nodePairsOfPlaces (arithFrobC q k N) hwW₀) hpole
  rw [h0] at hv₂
  have h00 : (arithFrobC q k N • w).HasValue (0 : ↥(modularFunctionFieldC k N)) 0 := by
    simpa using Place.hasValue_algebraMap (arithFrobC q k N • w) (0 : k)
  have hc0 : cv = 0 := hv₂.unique h00
  rw [hc0] at hv₁
  obtain ⟨-, h | h⟩ := (Place.hasValue_iff_mem_and_eq_or_ord_sub_pos _ _ _).mp hv₁
  · exact absurd (by simpa using h) hne
  · simpa using h

theorem residue₁_unit [IsAlgClosed k] [DecidableEq k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) {w : Place k (modularFunctionFieldC k N)} (hwW₀ : w ∈ W₀)
    (hreg : R.RegularityLaw W₀) (v : ↥(R.nodeIntegersOver K w)) (hv : IsUnit v) :
    R.nodeResidue₁ w ⟨v, v.2.1⟩ ≠ 0 ∧ w.ord (R.nodeResidue₁ w ⟨v, v.2.1⟩) = 0 := by
  have key := ModularCurve.PlaceSpecialization.ProlongationTuple.ord_nodeResidue_nonneg_of_regularityLaw
    R W₀ hreg K w hwW₀
  obtain ⟨vu, hvu⟩ := hv
  have hmul : v * (↑(vu⁻¹) : ↥(R.nodeIntegersOver K w)) = 1 := by rw [← hvu]; exact vu.mul_inv
  have hmul' : (⟨(v : ↥(modularFunctionFieldBar (N * q))), v.2.1⟩ : ↥(R.nodeIntegers w)) *
      ⟨((↑(vu⁻¹) : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))), (↑(vu⁻¹) : ↥(R.nodeIntegersOver K w)).2.1⟩ = 1 := by
    apply Subtype.ext
    have := congrArg (fun t : ↥(R.nodeIntegersOver K w) => (t : ↥(modularFunctionFieldBar (N * q)))) hmul
    simpa using this
  have hres : R.nodeResidue₁ w ⟨v, v.2.1⟩ *
      R.nodeResidue₁ w ⟨((↑(vu⁻¹) : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))), (↑(vu⁻¹) : ↥(R.nodeIntegersOver K w)).2.1⟩ = 1 := by
    rw [← map_mul, hmul', map_one]
  have hne : R.nodeResidue₁ w ⟨v, v.2.1⟩ ≠ 0 := left_ne_zero_of_mul_eq_one hres
  have hne' := right_ne_zero_of_mul_eq_one hres
  refine ⟨hne, ?_⟩
  have hsum := Place.ord_mul w hne hne'
  rw [hres, Place.ord_one] at hsum
  have h1 := (key v).1
  have h2 := (key (↑(vu⁻¹) : ↥(R.nodeIntegersOver K w))).1
  omega

theorem isUnit_evalAt_mul_zpow [IsAlgClosed k] [DecidableEq k]
    (w : Place k (modularFunctionFieldC k N))
    (hvalA : R.ValueIntegralityLaw w)
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) (hwW₀ : w ∈ W₀) (hreg : R.RegularityLaw W₀)
    (An : Annulus A ↥(modularFunctionFieldBar (N * q)))
    (hdom : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V ∈ An.dom ↔ P.reduceFst V = w)
    (hz₁ : An.param ∈ R.R₁.integers)
    (hzres : R.R₁.residue ⟨An.param, hz₁⟩ ≠ 0)
    (hzord : w.ord (R.residue₁ ⟨An.param, hz₁⟩) = 1)
    (f : ↥(modularFunctionFieldBar (N * q))) (hf₁ : f ∈ R.R₁.integers) (hfres : R.R₁.residue ⟨f, hf₁⟩ ≠ 0)
    (hf0 : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → V.ord f = 0)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    ∃ h : V.evalAt f * (V.evalAt An.param) ^ (-(w.ord (R.residue₁ ⟨f, hf₁⟩))) ∈ A,
      IsUnit (⟨_, h⟩ : A) := by
  classical

  set n : ℤ := w.ord (R.residue₁ ⟨f, hf₁⟩) with hn
  set z : ↥(modularFunctionFieldBar (N * q)) := An.param with hz

  have hzu : IsUnit (⟨z, hz₁⟩ : ↥(R.R₁.integers)) := R.R₁.isUnit_of_residue_ne_zero hzres
  have hfu : IsUnit (⟨f, hf₁⟩ : ↥(R.R₁.integers)) := R.R₁.isUnit_of_residue_ne_zero hfres
  have hz0 : z ≠ 0 := ne_zero_of_isUnit_mk R.R₁.integers hz₁ hzu
  have hf0' : f ≠ 0 := ne_zero_of_isUnit_mk R.R₁.integers hf₁ hfu

  have hzfacts : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
      V'.IsRational ∧ z ∈ V'.toValuationSubring ∧ V'.evalAt z ≠ 0 ∧ V'.ord z = 0 := by
    intro V' hV'
    obtain ⟨hrat, hmem, -, hne, -⟩ := An.mem_dom V' ((hdom V').mpr hV')
    exact ⟨hrat, hmem, hne, ord_eq_zero_of_evalAt_ne_zero V' hmem hne⟩
  obtain ⟨hVrat, hzV, hzV0, hzordV⟩ := hzfacts V hV

  obtain ⟨g, hg⟩ : ∃ g : ↥(modularFunctionFieldBar (N * q)), g = f * z ^ (-n) := ⟨_, rfl⟩
  have hg0 : g ≠ 0 := by rw [hg]; exact mul_ne_zero hf0' (zpow_ne_zero _ hz0)
  have hordg : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
      V'.ord g = 0 := by
    intro V' hV'
    rw [hg, Place.ord_mul _ hf0' (zpow_ne_zero _ hz0), Place.ord_zpow, hf0 V' hV', (hzfacts V' hV').2.2.2]
    ring
  have hzn : z ^ (-n) ∈ R.R₁.integers := zpow_mem_of_isUnit_mk R.R₁.integers hz₁ hzu (-n)
  have hg₁ : g ∈ R.R₁.integers := by rw [hg]; exact mul_mem hf₁ hzn
  have hgmk : (⟨g, hg₁⟩ : ↥(R.R₁.integers)) = ⟨f, hf₁⟩ * ⟨z ^ (-n), hzn⟩ := Subtype.ext hg
  have hres₁g : R.residue₁ ⟨g, hg₁⟩ = R.residue₁ ⟨f, hf₁⟩ * (R.residue₁ ⟨z, hz₁⟩) ^ (-n) := by
    rw [hgmk, map_mul, map_mk_zpow R.R₁.integers hz₁ hzu (-n) R.residue₁]
  have hfres' : R.residue₁ ⟨f, hf₁⟩ ≠ 0 := by
    rw [R.residue₁_apply]; exact (map_ne_zero R.ι).mpr hfres
  have hzres' : R.residue₁ ⟨z, hz₁⟩ ≠ 0 := by
    rw [R.residue₁_apply]; exact (map_ne_zero R.ι).mpr hzres
  have hgres' : R.residue₁ ⟨g, hg₁⟩ ≠ 0 := by
    rw [hres₁g]; exact mul_ne_zero hfres' (zpow_ne_zero _ hzres')
  have hgres : R.R₁.residue ⟨g, hg₁⟩ ≠ 0 := by
    intro h; apply hgres'; rw [R.residue₁_apply, h, map_zero]
  have hgu : IsUnit (⟨g, hg₁⟩ : ↥(R.R₁.integers)) := R.R₁.isUnit_of_residue_ne_zero hgres
  have hgord : w.ord (R.residue₁ ⟨g, hg₁⟩) = 0 := by
    rw [hres₁g, Place.ord_mul _ hfres' (zpow_ne_zero _ hzres'), Place.ord_zpow, hzord, ← hn]
    ring

  obtain ⟨hfV, -⟩ := Place.exists_isUnit_of_ord_eq_zero V hf0' (hf0 V hV)
  have hval : V.evalAt f * V.evalAt z ^ (-n) = V.evalAt g := by
    rw [hg]; exact (evalAt_mul_zpow_neg V hVrat hfV hzV hz0 hzordV n).symm
  rw [hval]

  have hgmemV : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
      g ∈ V'.toValuationSubring ∧ g⁻¹ ∈ V'.toValuationSubring := by
    intro V' hV'
    obtain ⟨hm, -⟩ := Place.exists_isUnit_of_ord_eq_zero V' hg0 (hordg V' hV')
    exact ⟨hm, inv_mem_of_ord_eq_zero V' hm hg0 (hordg V' hV')⟩

  obtain ⟨d, hdg, hdres⟩ := R.R₂.exists_smul_mem g hg0
  have hd0 : d ≠ 0 := R.R₂.smul_const_ne_zero hdg hdres
  have hsmul : (d • g : ↥(modularFunctionFieldBar (N * q))) = algebraMap (AlgebraicClosure ℚ) _ d * g :=
    Algebra.smul_def d g
  have hdgu : IsUnit (⟨d • g, hdg⟩ : ↥(R.R₂.integers)) := R.R₂.isUnit_of_residue_ne_zero hdres
  by_cases hdA : d ∈ A
  · by_cases hdiA : d⁻¹ ∈ A
    ·
      have hdR₁ : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d ∈ R.R₁.integers :=
        (R.R₁.algebraMap_mem_iff d).mpr hdA
      have hdiR₂ : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d⁻¹ ∈ R.R₂.integers :=
        (R.R₂.algebraMap_mem_iff d⁻¹).mpr hdiA
      have hdiR₁ : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d⁻¹ ∈ R.R₁.integers :=
        (R.R₁.algebraMap_mem_iff d⁻¹).mpr hdiA
      have hH₁ : (d • g : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₁.integers := by
        rw [hsmul]; exact mul_mem hdR₁ hg₁
      have hHinv : (d • g : ↥(modularFunctionFieldBar (N * q)))⁻¹
          = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d⁻¹ * g⁻¹ := by
        rw [hsmul, mul_inv, map_inv₀]
      have hHi₂ : (d • g : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ R.R₂.integers :=
        inv_mem_of_isUnit_mk R.R₂.integers hdg hdgu
      have hHi₁ : (d • g : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ R.R₁.integers := by
        rw [hHinv]; exact mul_mem hdiR₁ (inv_mem_of_isUnit_mk R.R₁.integers hg₁ hgu)
      have hH0 : (d • g : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := smul_ne_zero hd0 hg0
      have hHnode : (d • g : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w := by
        refine ⟨hH₁, hdg, fun V' hV' => ?_⟩
        rw [hsmul]; exact mul_mem (V'.algebraMap_mem' d) (hgmemV V' hV').1
      have hHinode : (d • g : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ R.nodeIntegers w := by
        refine ⟨hHi₁, hHi₂, fun V' hV' => ?_⟩
        rw [hHinv]; exact mul_mem (V'.algebraMap_mem' d⁻¹) (hgmemV V' hV').2
      have hA₂ := hvalA _ hHnode V hV
      have hA₁ := hvalA _ hHinode V hV
      have hHu := isUnit_mk_evalAt_of_inv A V hVrat hH0 (hHnode.2.2 V hV) (hHinode.2.2 V hV) hA₂ hA₁

      have hgeq : V.evalAt g = d⁻¹ * V.evalAt (d • g) := by
        have : g = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d⁻¹ * (d • g) := by
          rw [hsmul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd0, map_one, one_mul]
        conv_lhs => rw [this]
        rw [V.evalAt_mul hVrat (V.algebraMap_mem' d⁻¹) (hHnode.2.2 V hV), evalAt_algebraMap]
      rw [hgeq]
      have hdiu : IsUnit (⟨d⁻¹, hdiA⟩ : ↥A) :=
        isUnit_iff_exists_inv.mpr ⟨⟨d, hdA⟩, Subtype.ext (inv_mul_cancel₀ hd0)⟩
      refine ⟨mul_mem hdiA hA₂, ?_⟩
      have : (⟨d⁻¹ * V.evalAt (d • g), mul_mem hdiA hA₂⟩ : ↥A) = ⟨d⁻¹, hdiA⟩ * ⟨V.evalAt (d • g), hA₂⟩ := rfl
      rw [this]
      exact hdiu.mul hHu
    ·
      exfalso
      have hresd : IsLocalRing.residue ↥A ⟨d, hdA⟩ = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact fun hu' => hdiA ((isUnit_mk_iff_inv_mem A hdA hd0).mp hu')
      obtain ⟨hgi₁, hgi₁map⟩ := inv_mem_and_map_mk_inv (E := ↥(modularFunctionFieldC k N)) R.R₁.integers hg₁ hgu
      have hginv : g⁻¹ = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d * (d • g)⁻¹ := by
        rw [hsmul, mul_inv_rev, mul_comm g⁻¹, ← mul_assoc, ← map_inv₀, ← map_mul, mul_inv_cancel₀ hd0,
          map_one, one_mul]
      have hgi₂ : g⁻¹ ∈ R.R₂.integers := by
        rw [hginv]
        exact mul_mem ((R.R₂.algebraMap_mem_iff d).mpr hdA) (inv_mem_of_isUnit_mk R.R₂.integers hdg hdgu)
      have hgi₂res : R.residue₂ ⟨g⁻¹, hgi₂⟩ = 0 := by
        have hmk : (⟨g⁻¹, hgi₂⟩ : ↥(R.R₂.integers)) =
            ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d, (R.R₂.algebraMap_mem_iff d).mpr hdA⟩ *
            ⟨(d • g)⁻¹, inv_mem_of_isUnit_mk R.R₂.integers hdg hdgu⟩ := Subtype.ext hginv
        have hconst : R.R₂.residue ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d,
            (R.R₂.algebraMap_mem_iff d).mpr hdA⟩ = 0 := by
          have h' := R.R₂.residue_algebraMap ⟨d, hdA⟩
          rw [hresd, map_zero] at h'
          exact h'
        rw [R.residue₂_apply, hmk, map_mul, hconst, zero_mul, map_zero]
      have hgi₁res : R.residue₁ ⟨g⁻¹, hgi₁⟩ ≠ 0 := by
        rw [hgi₁map R.residue₁]; exact inv_ne_zero hgres'
      have hgi₁ord : w.ord (R.residue₁ ⟨g⁻¹, hgi₁⟩) = 0 := by
        rw [hgi₁map R.residue₁, Place.ord_inv, hgord, neg_zero]
      have hpole : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
          0 ≤ V'.ord g⁻¹ := fun V' hV' => by rw [Place.ord_inv, hordg V' hV', neg_zero]
      have := ord_residue₁_pos_of_residue₂_eq_zero R W₀ hwW₀ hreg g⁻¹ hgi₂ hgi₁ hpole hgi₂res hgi₁res
      omega
  ·
    exfalso
    have hdiA : d⁻¹ ∈ A := (A.mem_or_inv_mem d).resolve_left hdA
    have hresdi : IsLocalRing.residue ↥A ⟨d⁻¹, hdiA⟩ = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu'
      apply hdA
      have := (isUnit_mk_iff_inv_mem A hdiA (inv_ne_zero hd0)).mp hu'
      rwa [inv_inv] at this
    have hgeq' : g = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d⁻¹ * (d • g) := by
      rw [hsmul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd0, map_one, one_mul]
    have hg₂ : g ∈ R.R₂.integers := by
      rw [hgeq']
      exact mul_mem ((R.R₂.algebraMap_mem_iff d⁻¹).mpr hdiA) hdg
    have hg₂res : R.residue₂ ⟨g, hg₂⟩ = 0 := by
      have hmk : (⟨g, hg₂⟩ : ↥(R.R₂.integers)) =
          ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d⁻¹, (R.R₂.algebraMap_mem_iff d⁻¹).mpr hdiA⟩ *
          ⟨d • g, hdg⟩ := Subtype.ext hgeq'
      have hconst : R.R₂.residue ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d⁻¹,
          (R.R₂.algebraMap_mem_iff d⁻¹).mpr hdiA⟩ = 0 := by
        have h' := R.R₂.residue_algebraMap ⟨d⁻¹, hdiA⟩
        rw [hresdi, map_zero] at h'
        exact h'
      rw [R.residue₂_apply, hmk, map_mul, hconst, zero_mul, map_zero]
    have hpole : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
        0 ≤ V'.ord g := fun V' hV' => (hordg V' hV').ge
    have := ord_residue₁_pos_of_residue₂_eq_zero R W₀ hwW₀ hreg g hg₂ hg₁ hpole hg₂res hgres'
    omega

end Ws34.EndAttachFst

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (hord : R.OrderLawFixed)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hvalA : R.ValueIntegralityLaw w)
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) (hwW₀ : w ∈ W₀) (hreg : R.RegularityLaw W₀)
    (hres : ∀ g : ↥(R.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
    (hσπ : σ π = algebraMap _ _ (R.nodeConst K w ϖ))
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0 →
          w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0 →
          (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (c : R.NodeCoordinates K w) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u)
    (hy₁ : R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩ ≠ 0 ∧ w.ord (R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩) = 1)
    (An : Annulus A ↥(modularFunctionFieldBar (N * q)))
    (hdom : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V' ∈ An.dom ↔ (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))
    (hparam : An.param = (↑c.y : ↥(modularFunctionFieldBar (N * q)))) (hmod : (An.modulus : AlgebraicClosure ℚ) = (ϖ : AlgebraicClosure ℚ) ^ E₀) :
    letI : Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N) :=
      ((algebraMap k ↥(modularFunctionFieldC k N)).comp R.redBar).toAlgebra
    ∀ (C₁ : ComponentChart A ↥(modularFunctionFieldBar (N * q)) ↥(modularFunctionFieldC k N)) (x₁ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N)),
      x₁ ∈ C₁.nodes →
      (∀ f : ↥(modularFunctionFieldBar (N * q)), f ∈ C₁.integers ↔ f ∈ R.R₁.integers) →
      (∀ (f : ↥(modularFunctionFieldBar (N * q))) (hC : f ∈ C₁.integers) (h₁ : f ∈ R.R₁.integers),
        (C₁.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₁.residue ⟨f, h₁⟩ ≠ 0) ∧
        x₁.ord (C₁.residue ⟨f, hC⟩) = w.ord (R.residue₁ ⟨f, h₁⟩)) →
      An.IsAttached C₁ x₁ := by
  letI : Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N) :=
    ((algebraMap k ↥(modularFunctionFieldC k N)).comp R.redBar).toAlgebra
  intro C₁ x₁ hx₁n hint hdict
  have hdom₀ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V ∈ An.dom ↔ P.reduceFst V = w :=
    Ws34.EndAttach.mem_dom_iff_reduceFst_eq P hqN w hw hdom

  have hz₁ : An.param ∈ R.R₁.integers := by rw [hparam]; exact c.y.2.1.1
  have hzres : R.R₁.residue ⟨An.param, hz₁⟩ ≠ 0 := by
    intro h
    apply hy₁.1
    have e : (⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1.1⟩ : ↥(R.R₁.integers)) = ⟨An.param, hz₁⟩ :=
      Subtype.ext hparam.symm
    rw [nodeResidue₁_apply, residue₁_apply, e, h, map_zero]
  have hzord : w.ord (R.residue₁ ⟨An.param, hz₁⟩) = 1 := by
    have e : (⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1.1⟩ : ↥(R.R₁.integers)) = ⟨An.param, hz₁⟩ :=
      Subtype.ext hparam.symm
    rw [← e]; exact hy₁.2
  have hzC : An.param ∈ C₁.integers := (hint _).mpr hz₁
  refine ⟨hx₁n, hzC, ?_, ?_⟩
  · rw [(hdict _ hzC hz₁).2]; exact hzord
  · intro f hfC hfres hf0 V hV
    have hf₁ : f ∈ R.R₁.integers := (hint f).mp hfC
    have hfres₁ : R.R₁.residue ⟨f, hf₁⟩ ≠ 0 := (hdict f hfC hf₁).1.mp hfres
    have hn : x₁.ord (C₁.residue ⟨f, hfC⟩) = w.ord (R.residue₁ ⟨f, hf₁⟩) := (hdict f hfC hf₁).2
    rw [hn]
    have hVw : P.reduceFst V = w := (hdom₀ V).mp hV
    have hf0' : ∀ V', P.reduceFst V' = w → V'.ord f = 0 := fun V' h => hf0 V' ((hdom₀ V').mpr h)
    exact Ws34.EndAttachFst.isUnit_evalAt_mul_zpow R w hvalA W₀ hwW₀ hreg An hdom₀ hz₁ hzres hzord
      f hf₁ hfres₁ hf0' V hVw

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_isAttached_fst_of_ringEquiv_uvCrossingModel_of_regularityLaw
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isAttached_fst_of_ringEquiv_uvCrossingModel_of_regularityLaw (solution)

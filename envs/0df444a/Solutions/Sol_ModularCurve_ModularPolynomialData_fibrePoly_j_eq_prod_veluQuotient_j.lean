-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b1d998e5-3ebc-59f1-8b4d-8c94a5468650

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_exists_valuationSubring_with_transcendental_of_charZero
import Theorems.Thm_WittVector_exists_valuationSubring_lift_with_transcendental
import Theorems.Thm_WeierstrassCurve_transcendental_j_perturb
import Theorems.Thm_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"

set_option autoImplicit false

p2m_open "Polynomial ModularCurve WeierstrassCurve~map_veluTSum~map_veluT~map_veluW~map_veluWSum~specialize WeierstrassCurve.Affine IsLocalRing"

universe u

namespace A1Skeleton

noncomputable abbrev jQuot {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (ℓ : ℕ) (Q : W.toAffine.Point)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q (ℓ / 2))).Δ ≠ 0) : F :=
  @WeierstrassCurve.j F _ (W.veluQuotient (W.oddOrderSummingSet Q (ℓ / 2)))
    ⟨isUnit_iff_ne_zero.mpr hΔ⟩

def ProdFormula {F : Type*} [Field F] [DecidableEq F] {ℓ : ℕ} [NeZero ℓ]
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve F) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (Q : ι → W.toAffine.Point)
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) : Prop :=
  fibrePoly data.Φ W.j = ∏ i : ι, (X - C (jQuot W ℓ (Q i) (hΔ i)))

namespace Transport

universe uF

section MapPoint

variable {R S : Type*} [Field R] [Field S] [DecidableEq R] [DecidableEq S] (φ : R →+* S)
  (W : WeierstrassCurve R)

omit [DecidableEq R] [DecidableEq S] in
theorem nonsingular_map {x y : R} (h : W.toAffine.Nonsingular x y) :
    (W.map φ).toAffine.Nonsingular (φ x) (φ y) :=
  (Affine.map_nonsingular (W := W.toAffine) (f := φ) φ.injective x y).mpr h

def mapFun : W.toAffine.Point → (W.map φ).toAffine.Point
  | 0 => 0
  | .some x y h => .some (φ x) (φ y) (nonsingular_map φ W h)

omit [DecidableEq R] [DecidableEq S] in
theorem mapFun_zero : mapFun φ W 0 = 0 := rfl

omit [DecidableEq R] [DecidableEq S] in
theorem mapFun_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    mapFun φ W (.some x y h) = .some (φ x) (φ y) (nonsingular_map φ W h) := rfl

theorem mapFun_add (P Q : W.toAffine.Point) :
    mapFun φ W (P + Q) = mapFun φ W P + mapFun φ W Q := by
  have hneg : ∀ x y : R, (W.map φ).toAffine.negY (φ x) (φ y) = φ (W.toAffine.negY x y) :=
    fun x y => Affine.map_negY (W' := W.toAffine) φ x y
  have hslope : ∀ x₁ x₂ y₁ y₂ : R,
      (W.map φ).toAffine.slope (φ x₁) (φ x₂) (φ y₁) (φ y₂) = φ (W.toAffine.slope x₁ x₂ y₁ y₂) :=
    fun x₁ x₂ y₁ y₂ => Affine.map_slope (W := W.toAffine) φ x₁ x₂ y₁ y₂
  have haddX : ∀ x₁ x₂ ℓ : R,
      (W.map φ).toAffine.addX (φ x₁) (φ x₂) (φ ℓ) = φ (W.toAffine.addX x₁ x₂ ℓ) :=
    fun x₁ x₂ ℓ => Affine.map_addX (W' := W.toAffine) φ x₁ x₂ ℓ
  have haddY : ∀ x₁ x₂ y₁ ℓ : R,
      (W.map φ).toAffine.addY (φ x₁) (φ x₂) (φ y₁) (φ ℓ) = φ (W.toAffine.addY x₁ x₂ y₁ ℓ) :=
    fun x₁ x₂ y₁ ℓ => Affine.map_addY (W' := W.toAffine) (f := φ) (x₁ := x₁) (x₂ := x₂)
      (y₁ := y₁) (ℓ := ℓ)
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    exact (Affine.Point.add_of_Y_eq (congrArg φ hxy.1) (by rw [hxy.2, hneg])).symm
  · have hxy' : ¬(φ x₁ = φ x₂ ∧ φ y₁ = (W.map φ).toAffine.negY (φ x₂) (φ y₂)) := fun h =>
      hxy ⟨φ.injective h.1, φ.injective (by rw [hneg] at h; exact h.2)⟩
    rw [Affine.Point.add_some hxy]
    show mapFun φ W _ = Affine.Point.some _ _ _ + Affine.Point.some _ _ _
    rw [Affine.Point.add_some hxy', mapFun_some]
    congr 1
    · rw [hslope, haddX]
    · rw [hslope, haddY]

def mapPoint : W.toAffine.Point →+ (W.map φ).toAffine.Point where
  toFun := mapFun φ W
  map_zero' := rfl
  map_add' := mapFun_add φ W

theorem mapPoint_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    mapPoint φ W (.some x y h) = .some (φ x) (φ y) (nonsingular_map φ W h) := rfl

theorem mapPoint_injective : Function.Injective (mapPoint φ W) := by
  intro P Q hPQ
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · exact absurd hPQ.symm (Affine.Point.some_ne_zero _)
  · exact absurd hPQ (Affine.Point.some_ne_zero _)
  · have h := hPQ
    change Affine.Point.some (φ x₁) (φ y₁) _ = Affine.Point.some (φ x₂) (φ y₂) _ at h
    simp only [Affine.Point.some.injEq] at h
    obtain ⟨hx, hy⟩ := h
    cases φ.injective hx
    cases φ.injective hy
    rfl

theorem coordsOrZero_mapPoint (P : W.toAffine.Point) :
    (mapPoint φ W P).coordsOrZero = Prod.map φ φ P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · show ((0 : S), (0 : S)) = (φ 0, φ 0)
    simp
  · rfl

theorem addOrderOf_mapPoint (P : W.toAffine.Point) :
    addOrderOf (mapPoint φ W P) = addOrderOf P :=
  addOrderOf_injective (mapPoint φ W) (mapPoint_injective φ W) P

theorem oddOrderSummingSet_mapPoint (Q : W.toAffine.Point) (n : ℕ) :
    (W.map φ).oddOrderSummingSet (mapPoint φ W Q) n =
      (W.oddOrderSummingSet Q n).image (Prod.map φ φ) := by
  simp only [WeierstrassCurve.oddOrderSummingSet, Finset.image_image]
  refine Finset.image_congr fun k _ => ?_
  show (k • mapPoint φ W Q).coordsOrZero = Prod.map φ φ (k • Q).coordsOrZero
  rw [← map_nsmul, coordsOrZero_mapPoint]

end MapPoint

section Velu

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)

theorem map_veluT (x y : R) : φ (W.veluT x y) = (W.map φ).veluT (φ x) (φ y) := by
  simp [WeierstrassCurve.veluT, WeierstrassCurve.veluGx, WeierstrassCurve.veluGy, map_ofNat]

theorem map_veluW (x y : R) : φ (W.veluW x y) = (W.map φ).veluW (φ x) (φ y) := by
  simp [WeierstrassCurve.veluW, WeierstrassCurve.veluU, WeierstrassCurve.veluT,
    WeierstrassCurve.veluGx, WeierstrassCurve.veluGy, map_ofNat]

variable [DecidableEq S]

theorem map_veluTSum (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    φ (W.veluTSum T) = (W.map φ).veluTSum (T.image (Prod.map φ φ)) := by
  rw [WeierstrassCurve.veluTSum, WeierstrassCurve.veluTSum, Finset.sum_image hφ, map_sum]
  exact Finset.sum_congr rfl fun P _ => map_veluT φ W P.1 P.2

theorem map_veluWSum (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    φ (W.veluWSum T) = (W.map φ).veluWSum (T.image (Prod.map φ φ)) := by
  rw [WeierstrassCurve.veluWSum, WeierstrassCurve.veluWSum, Finset.sum_image hφ, map_sum]
  exact Finset.sum_congr rfl fun P _ => map_veluW φ W P.1 P.2

theorem veluQuotient_map (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    (W.veluQuotient T).map φ = (W.map φ).veluQuotient (T.image (Prod.map φ φ)) := by
  ext
  · rfl
  · rfl
  · rfl
  · show φ (W.a₄ - 5 * W.veluTSum T) = _
    rw [WeierstrassCurve.veluQuotient_a₄, map_sub, map_mul, map_ofNat, map_veluTSum φ W T hφ]
    rfl
  · show φ (W.a₆ - W.b₂ * W.veluTSum T - 7 * W.veluWSum T) = _
    rw [WeierstrassCurve.veluQuotient_a₆, map_sub, map_sub, map_mul, map_mul, map_ofNat,
      map_veluTSum φ W T hφ, map_veluWSum φ W T hφ, ← WeierstrassCurve.map_b₂]
    rfl

end Velu

theorem isRoot_map_iff {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (Φ : Polynomial (Polynomial ℤ)) (a b : R) :
    (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom S) (φ a))).IsRoot (φ b) ↔
      (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) a)).IsRoot b := by
  have hcomp : Polynomial.eval₂RingHom (Int.castRingHom S) (φ a) =
      φ.comp (Polynomial.eval₂RingHom (Int.castRingHom R) a) := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · simp
    · simp
  rw [hcomp, ← Polynomial.map_map, Polynomial.IsRoot.def, Polynomial.IsRoot.def, Polynomial.eval_map,
    Polynomial.eval₂_hom, map_eq_zero_iff φ hφ]

theorem j_congr {F : Type*} [Field F] {A B : WeierstrassCurve F} (h : A = B)
    (hA : A.IsElliptic) (hB : B.IsElliptic) : @WeierstrassCurve.j F _ A hA = @WeierstrassCurve.j F _ B hB := by
  subst h
  rfl

theorem fibrePoly_map_ringHom {R : Type*} [CommRing R] {κ : Type*} [Field κ] (f : R →+* κ)
    (Φ : Polynomial (Polynomial ℤ)) (a : R) :
    fibrePoly Φ (f a) = (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) a)).map f := by
  have hcomp : Polynomial.eval₂RingHom (Int.castRingHom κ) (f a) =
      f.comp (Polynomial.eval₂RingHom (Int.castRingHom R) a) := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · simp
    · simp
  rw [fibrePoly, hcomp, ← Polynomial.map_map]

theorem fibrePoly_map {K : Type*} [Field K] {κ : Type*} [Field κ] (ι : K →+* κ)
    (Φ : Polynomial (Polynomial ℤ)) (a : K) :
    fibrePoly Φ (ι a) = (fibrePoly Φ a).map ι :=
  fibrePoly_map_ringHom ι Φ a

end Transport

open Transport

theorem prodFormula_of_map
    {K : Type*} [Field K] [DecidableEq K] {κ : Type*} [Field κ] [DecidableEq κ]
    (ιh : K →+* κ) {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ)
    (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (Q : ι → W.toAffine.Point)
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0)
    (hΔ' : ∀ i, ((W.map ιh).veluQuotient
      ((W.map ιh).oddOrderSummingSet (mapPoint ιh W (Q i)) (ℓ / 2))).Δ ≠ 0)
    (h : ProdFormula data (W.map ιh) (fun i => mapPoint ιh W (Q i)) hΔ') :
    ProdFormula data W Q hΔ := by
  classical
  unfold ProdFormula at h ⊢
  apply Polynomial.map_injective ιh ιh.injective
  have hcurve : ∀ i, (W.map ιh).veluQuotient ((W.map ιh).oddOrderSummingSet (mapPoint ιh W (Q i)) (ℓ / 2))
      = (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).map ιh := fun i => by
    rw [oddOrderSummingSet_mapPoint ιh W (Q i) (ℓ / 2),
      veluQuotient_map ιh W _ (Function.Injective.prodMap ιh.injective ιh.injective).injOn]
  have hj : ∀ i, jQuot (W.map ιh) ℓ (mapPoint ιh W (Q i)) (hΔ' i) = ιh (jQuot W ℓ (Q i) (hΔ i)) := by
    intro i
    unfold jQuot
    haveI : (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).IsElliptic :=
      ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩
    rw [j_congr (hcurve i) ⟨isUnit_iff_ne_zero.mpr (hΔ' i)⟩ inferInstance, WeierstrassCurve.map_j]
  rw [← fibrePoly_map, ← WeierstrassCurve.map_j, h, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hj]

theorem lift_dispatch
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (WA : WeierstrassCurve A) (hΔA : (WA.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q₀ : (WA.map (residue A)).toAffine.Point) (hQ₀ : ℓ • Q₀ = 0) :
    ∃ Q : (WA.map A.subtype).toAffine.Point, ℓ • Q = 0 ∧ reduceHom hΔA Q = Q₀ := by
  exact _root_.WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero A WA hΔA hℓ Q₀ hQ₀

theorem prodFormula_specialFibre
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (WA : WeierstrassCurve A) (hΔA : (WA.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓ : (ℓ : ResidueField A) ≠ 0)
    (hlift : ∀ Q₀ : (WA.map (residue A)).toAffine.Point, ℓ • Q₀ = 0 →
      ∃ Q : (WA.map A.subtype).toAffine.Point, ℓ • Q = 0 ∧ reduceHom hΔA Q = Q₀)
    (data : ModularPolynomialData ℓ)
    (htr : ∀ hΔL : (WA.map A.subtype).Δ ≠ 0,
      Transcendental ℚ (@WeierstrassCurve.j L _ (WA.map A.subtype) ⟨isUnit_iff_ne_zero.mpr hΔL⟩))
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q' : ι → (WA.map (residue A)).toAffine.Point) (hQ' : ∀ i, addOrderOf (Q' i) = ℓ)
    (hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (Q' i))
    [hE : (WA.map (residue A)).IsElliptic]
    (hΔ' : ∀ i, ((WA.map (residue A)).veluQuotient
      ((WA.map (residue A)).oddOrderSummingSet (Q' i) (ℓ / 2))).Δ ≠ 0) :
    ProdFormula data (WA.map (residue A)) Q' hΔ' := by
  classical
  have hℓP : ℓ.Prime := Fact.out

  have hresΔ : residue A WA.Δ ≠ 0 := by rwa [← map_Δ]
  have hΔunit : IsUnit WA.Δ := by
    by_contra h
    exact hresΔ ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
  haveI hWA : WA.IsElliptic := ⟨hΔunit⟩
  have hΔL : (WA.map A.subtype).Δ ≠ 0 := by
    rw [map_Δ]
    intro h
    exact hΔunit.ne_zero (Subtype.val_injective (by simpa using h))
  haveI : (WA.map A.subtype).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔL⟩

  have hlift' : ∀ i, ∃ Qt : (WA.map A.subtype).toAffine.Point,
      ℓ • Qt = 0 ∧ reduceHom hΔA Qt = Q' i := fun i =>
    hlift (Q' i) (by rw [← hQ' i]; exact addOrderOf_nsmul_eq_zero (Q' i))
  choose Qt hQt using hlift'

  have hQt_ne : ∀ i, Qt i ≠ 0 := by
    intro i h
    have h1 : Q' i = 0 := by rw [← (hQt i).2, h, map_zero]
    have h2' : addOrderOf (Q' i) = 1 := by rw [h1, addOrderOf_zero]
    rw [hQ' i] at h2'
    exact hℓP.one_lt.ne' h2'
  have hQt_ord : ∀ i, addOrderOf (Qt i) = ℓ := fun i =>
    addOrderOf_eq_prime (hQt i).1 (hQt_ne i)
  have hQt_inj : Function.Injective fun i => AddSubgroup.zmultiples (Qt i) := by
    intro i i' h
    apply hQ'inj
    simp only at h ⊢
    have := congrArg (AddSubgroup.map (reduceHom hΔA)) h
    rwa [AddMonoidHom.map_zmultiples, AddMonoidHom.map_zmultiples, (hQt i).2, (hQt i').2] at this

  have hodd : 2 * (ℓ / 2) + 1 = ℓ := by
    rcases hℓP.eq_two_or_odd' with h | h
    · exact absurd h hℓ2
    · exact Nat.two_mul_div_two_add_one_of_odd h
  have hΔt : ∀ i, ((WA.map A.subtype).veluQuotient
      ((WA.map A.subtype).oddOrderSummingSet (Qt i) (ℓ / 2))).Δ ≠ 0 := fun i =>
    _root_.WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq (WA.map A.subtype) (ℓ / 2) (Qt i) (by rw [hodd]; exact hQt_ord i)

  have hT := _root_.ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed (K := L) hℓ2 data (WA.map A.subtype) (htr hΔL) hι Qt hQt_ord hQt_inj hΔt

  have hS : ∀ i, ∃ V : WeierstrassCurve A,
      V.map A.subtype = (WA.map A.subtype).veluQuotient ((WA.map A.subtype).oddOrderSummingSet (Qt i) (ℓ / 2)) ∧
      V.map (residue A) = (WA.map (residue A)).veluQuotient
        ((WA.map (residue A)).oddOrderSummingSet (reduceHom hΔA (Qt i)) (ℓ / 2)) := fun i =>
    _root_.WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom A WA hΔA hℓ (Qt i) (hQt_ord i) (Nat.div_lt_self hℓP.pos one_lt_two)
  choose V hV using hS

  have hVres : ∀ i, (V i).map (residue A) =
      (WA.map (residue A)).veluQuotient ((WA.map (residue A)).oddOrderSummingSet (Q' i) (ℓ / 2)) := by
    intro i; rw [(hV i).2, (hQt i).2]
  have hVunit : ∀ i, IsUnit (V i).Δ := by
    intro i
    by_contra h
    apply hΔ' i
    rw [← hVres i, map_Δ]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h)
  haveI hVell : ∀ i, (V i).IsElliptic := fun i => ⟨hVunit i⟩

  have hjgen : ∀ i, @WeierstrassCurve.j L _ ((WA.map A.subtype).veluQuotient
      ((WA.map A.subtype).oddOrderSummingSet (Qt i) (ℓ / 2))) ⟨isUnit_iff_ne_zero.mpr (hΔt i)⟩
        = A.subtype (V i).j := by
    intro i
    have e := (hV i).1
    have : ∀ (V' : WeierstrassCurve L) (hV' : V' = (V i).map A.subtype) (h' : V'.IsElliptic),
        @WeierstrassCurve.j L _ V' h' = A.subtype (V i).j := by
      rintro V' rfl h'; exact WeierstrassCurve.map_j (V i) A.subtype
    exact this _ e.symm _
  have hjres : ∀ i, jQuot (WA.map (residue A)) ℓ (Q' i) (hΔ' i) = residue A (V i).j := by
    intro i
    have e := hVres i
    have : ∀ (V' : WeierstrassCurve (ResidueField A)) (hV' : V' = (V i).map (residue A))
        (h' : V'.IsElliptic), @WeierstrassCurve.j _ _ V' h' = residue A (V i).j := by
      rintro V' rfl h'; exact WeierstrassCurve.map_j (V i) (residue A)
    exact this _ e.symm _

  set PA : Polynomial A := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) WA.j) with hPA
  set QA : Polynomial A := ∏ i, (X - C (V i).j) with hQA

  have hPAmap : ∀ {S : Type _} [CommRing S] (g : A →+* S),
      PA.map g = data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom S) (g WA.j)) := by
    intro S _ g
    rw [hPA, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' ?_ ?_
    · ext n; simp
    · simp
  have hPAgen : PA.map A.subtype = fibrePoly data.Φ (WA.map A.subtype).j := by
    rw [hPAmap, WeierstrassCurve.map_j]; rfl
  have hPAres : PA.map (residue A) = fibrePoly data.Φ (WA.map (residue A)).j := by
    rw [hPAmap]
    have : (WA.map (residue A)).j = residue A WA.j := WeierstrassCurve.map_j WA (residue A)
    rw [this]; rfl

  have hQAgen : QA.map A.subtype = ∏ i, (X - C (@WeierstrassCurve.j L _ ((WA.map A.subtype).veluQuotient
      ((WA.map A.subtype).oddOrderSummingSet (Qt i) (ℓ / 2))) ⟨isUnit_iff_ne_zero.mpr (hΔt i)⟩)) := by
    rw [hQA, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hjgen i]
  have hQAres : QA.map (residue A) = ∏ i, (X - C (jQuot (WA.map (residue A)) ℓ (Q' i) (hΔ' i))) := by
    rw [hQA, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hjres i]

  have hPQ : PA = QA := by
    apply Polynomial.map_injective A.subtype Subtype.val_injective
    rw [hPAgen, hQAgen]
    exact hT

  show fibrePoly data.Φ (WA.map (residue A)).j = ∏ i, (X - C (jQuot (WA.map (residue A)) ℓ (Q' i) (hΔ' i)))
  rw [← hPAres, ← hQAres, hPQ]

theorem main_charZero
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] [CharZero K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    ProdFormula data W Q hΔ := by
  classical

  obtain ⟨L, _, _, _, A, φ, hφ, ιh, hι_res, t, htA, htm, htr⟩ := _root_.WeierstrassCurve.exists_valuationSubring_with_transcendental_of_charZero K
  letI : DecidableEq L := Classical.decEq _
  letI : DecidableEq (ResidueField A) := Classical.decEq _

  let tA : A := ⟨t, htA⟩
  let WA : WeierstrassCurve A :=
    ⟨⟨φ W.a₁, hφ _⟩, ⟨φ W.a₂, hφ _⟩, ⟨φ W.a₃, hφ _⟩, ⟨φ W.a₄, hφ _⟩ + tA, ⟨φ W.a₆, hφ _⟩ + tA ^ 2⟩
  have htres : residue A tA = 0 := (residue_eq_zero_iff (R := A) tA).mpr htm
  have hWA_res : WA.map (residue A) = W.map ιh := by
    ext <;> simp [WA, WeierstrassCurve.map, hι_res, htres]
  have hWA_gen : WA.map A.subtype = ⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄ + t, φ W.a₆ + t ^ 2⟩ := by
    ext <;> rfl

  obtain ⟨hΔgen, hJ⟩ := _root_.WeierstrassCurve.transcendental_j_perturb (R := K) φ t htr W
  have htrWA : ∀ hΔL : (WA.map A.subtype).Δ ≠ 0,
      Transcendental ℚ (@WeierstrassCurve.j L _ (WA.map A.subtype) ⟨isUnit_iff_ne_zero.mpr hΔL⟩) := by
    intro hΔL
    rwa [j_congr hWA_gen ⟨isUnit_iff_ne_zero.mpr hΔL⟩ ⟨isUnit_iff_ne_zero.mpr hΔgen⟩]

  have hΔA : (WA.map (residue A)).Δ ≠ 0 := by
    rw [hWA_res, WeierstrassCurve.map_Δ]; exact (_root_.map_ne_zero ιh).mpr W.isUnit_Δ.ne_zero
  have hℓκ : (ℓ : ResidueField A) ≠ 0 := by
    rw [← map_natCast ιh, _root_.map_ne_zero]; exact Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero

  have key : ∀ (X : WeierstrassCurve (ResidueField A)) (hX : WA.map (residue A) = X)
      [X.IsElliptic] (Q' : ι → X.toAffine.Point) (hQ' : ∀ i, addOrderOf (Q' i) = ℓ)
      (hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (Q' i))
      (hΔ' : ∀ i, (X.veluQuotient (X.oddOrderSummingSet (Q' i) (ℓ / 2))).Δ ≠ 0),
      ProdFormula data X Q' hΔ' := by
    rintro X rfl _ Q' hQ' hQ'inj hΔ'
    exact prodFormula_specialFibre A WA hΔA hℓ2 hℓκ (lift_dispatch A WA hΔA hℓκ) data htrWA hι
      Q' hQ' hQ'inj hΔ'

  have hQ' : ∀ i, addOrderOf (mapPoint ιh W (Q i)) = ℓ := fun i => by rw [addOrderOf_mapPoint, hQ i]
  have hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (mapPoint ιh W (Q i)) := by
    intro i j hij
    apply hQinj
    have h1 : ∀ k, AddSubgroup.zmultiples (mapPoint ιh W (Q k))
        = (AddSubgroup.zmultiples (Q k)).map (mapPoint ιh W) := fun k =>
      (AddMonoidHom.map_zmultiples (mapPoint ιh W) (Q k)).symm
    simp only [h1] at hij
    exact AddSubgroup.map_injective (mapPoint_injective ιh W) hij
  have hΔ' : ∀ i, ((W.map ιh).veluQuotient
      ((W.map ιh).oddOrderSummingSet (mapPoint ιh W (Q i)) (ℓ / 2))).Δ ≠ 0 := fun i => by
    have hodd : ℓ = 2 * (ℓ / 2) + 1 := by
      have := (Fact.out : ℓ.Prime).eq_two_or_odd'.resolve_left hℓ2
      obtain ⟨m, hm⟩ := this; omega
    exact _root_.WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq (W.map ιh) (ℓ / 2) (mapPoint ιh W (Q i)) (by rw [hQ' i]; exact hodd)
  exact prodFormula_of_map ιh data W Q hΔ hΔ' (key (W.map ιh) hWA_res _ hQ' hQ'inj hΔ')

theorem main_charP
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] (q : ℕ) [Fact q.Prime] [CharP K q]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    ProdFormula data W Q hΔ := by
  classical
  haveI : PerfectRing K q := IsAlgClosed.perfectRing K q
  obtain ⟨L, _, _, _, A, φ, hφ, ιh, hι_res, t, htA, htm, htr⟩ := _root_.WittVector.exists_valuationSubring_lift_with_transcendental q K
  letI : DecidableEq L := Classical.decEq _
  letI : DecidableEq (ResidueField A) := Classical.decEq _

  haveI : CharZero (WittVector q K) := φ.charZero

  let τ : K → WittVector q K := WittVector.teichmuller q
  let W𝕎 : WeierstrassCurve (WittVector q K) := ⟨τ W.a₁, τ W.a₂, τ W.a₃, τ W.a₄, τ W.a₆⟩
  let tA : A := ⟨t, htA⟩
  let WA : WeierstrassCurve A :=
    ⟨⟨φ (τ W.a₁), hφ _⟩, ⟨φ (τ W.a₂), hφ _⟩, ⟨φ (τ W.a₃), hφ _⟩,
     ⟨φ (τ W.a₄), hφ _⟩ + tA, ⟨φ (τ W.a₆), hφ _⟩ + tA ^ 2⟩
  have htres : residue A tA = 0 := (residue_eq_zero_iff (R := A) tA).mpr htm
  have hWA_res : WA.map (residue A) = W.map ιh := by
    ext <;> simp [WA, τ, WeierstrassCurve.map, hι_res, htres]
  have hWA_gen : WA.map A.subtype =
      ⟨φ W𝕎.a₁, φ W𝕎.a₂, φ W𝕎.a₃, φ W𝕎.a₄ + t, φ W𝕎.a₆ + t ^ 2⟩ := by
    ext <;> rfl

  obtain ⟨hΔgen, hJ⟩ := _root_.WeierstrassCurve.transcendental_j_perturb (R := WittVector q K) φ t htr W𝕎
  have htrWA : ∀ hΔL : (WA.map A.subtype).Δ ≠ 0,
      Transcendental ℚ (@WeierstrassCurve.j L _ (WA.map A.subtype) ⟨isUnit_iff_ne_zero.mpr hΔL⟩) := by
    intro hΔL
    rwa [j_congr hWA_gen ⟨isUnit_iff_ne_zero.mpr hΔL⟩ ⟨isUnit_iff_ne_zero.mpr hΔgen⟩]

  have hΔA : (WA.map (residue A)).Δ ≠ 0 := by
    rw [hWA_res, WeierstrassCurve.map_Δ]; exact (_root_.map_ne_zero ιh).mpr W.isUnit_Δ.ne_zero
  have hℓκ : (ℓ : ResidueField A) ≠ 0 := by
    rw [← map_natCast ιh, _root_.map_ne_zero]; exact hℓK

  have key : ∀ (X : WeierstrassCurve (ResidueField A)) (hX : WA.map (residue A) = X)
      [X.IsElliptic] (Q' : ι → X.toAffine.Point) (hQ' : ∀ i, addOrderOf (Q' i) = ℓ)
      (hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (Q' i))
      (hΔ' : ∀ i, (X.veluQuotient (X.oddOrderSummingSet (Q' i) (ℓ / 2))).Δ ≠ 0),
      ProdFormula data X Q' hΔ' := by
    rintro X rfl _ Q' hQ' hQ'inj hΔ'
    exact prodFormula_specialFibre A WA hΔA hℓ2 hℓκ (lift_dispatch A WA hΔA hℓκ) data htrWA hι
      Q' hQ' hQ'inj hΔ'

  have hQ' : ∀ i, addOrderOf (mapPoint ιh W (Q i)) = ℓ := fun i => by rw [addOrderOf_mapPoint, hQ i]
  have hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (mapPoint ιh W (Q i)) := by
    intro i j hij
    apply hQinj
    have h1 : ∀ k, AddSubgroup.zmultiples (mapPoint ιh W (Q k))
        = (AddSubgroup.zmultiples (Q k)).map (mapPoint ιh W) := fun k =>
      (AddMonoidHom.map_zmultiples (mapPoint ιh W) (Q k)).symm
    simp only [h1] at hij
    exact AddSubgroup.map_injective (mapPoint_injective ιh W) hij
  have hΔ' : ∀ i, ((W.map ιh).veluQuotient
      ((W.map ιh).oddOrderSummingSet (mapPoint ιh W (Q i)) (ℓ / 2))).Δ ≠ 0 := fun i => by
    have hodd : ℓ = 2 * (ℓ / 2) + 1 := by
      have := (Fact.out : ℓ.Prime).eq_two_or_odd'.resolve_left hℓ2
      obtain ⟨m, hm⟩ := this; omega
    exact _root_.WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq (W.map ιh) (ℓ / 2) (mapPoint ιh W (Q i)) (by rw [hQ' i]; exact hodd)
  exact prodFormula_of_map ιh data W Q hΔ hΔ' (key (W.map ιh) hWA_res _ hQ' hQ'inj hΔ')

theorem main
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _
        (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by

  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hprime | rfl
  · haveI := Fact.mk hprime
    exact main_charP p hℓ2 hℓK data W hι Q hQ hQinj hΔ
  · haveI : CharZero K := CharP.charP_to_charZero K
    exact main_charZero hℓ2 data W hι Q hQ hQinj hΔ

end A1Skeleton

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _
        (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) :=
  A1Skeleton.main hℓ2 hℓK data W hι Q hQ hQinj hΔ

end S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j (solution)

-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c8ef6f40-1585-5285-ae4b-e0e31ee174e3

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental
import Theorems.Thm_HahnSeries_isAlgClosed_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

set_option autoImplicit false

open Polynomial ModularCurve WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace TDescent

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

theorem exists_cover {F : Type uF} [Field F] [IsAlgClosed F] {m : ℕ} (g : Fin m → F) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : IsAlgClosed K₀) (φ : K₀ →+* F), ∀ i, g i ∈ Set.range φ := by
  classical
  let ev : MvPolynomial (Fin m) ℤ →+* F := MvPolynomial.eval₂Hom (Int.castRingHom F) g
  haveI : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  let D : Type := MvPolynomial (Fin m) ℤ ⧸ RingHom.ker ev
  let ψ₁ : D →+* F := RingHom.kerLift ev
  have hψ₁ : Function.Injective ψ₁ := RingHom.kerLift_injective ev
  let L : Type := FractionRing D
  let ψ₂ : L →+* F := IsFractionRing.lift hψ₁
  let K₀ : Type := AlgebraicClosure L
  letI : Algebra L F := ψ₂.toAlgebra
  haveI : Module.IsTorsionFree L F :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [RingHom.algebraMap_toAlgebra]; exact ψ₂.injective)
  let ψ₃ : K₀ →ₐ[L] F := IsAlgClosed.lift
  refine ⟨K₀, inferInstance, inferInstance, ψ₃.toRingHom, fun i => ?_⟩
  refine ⟨algebraMap L K₀ (algebraMap D L (Ideal.Quotient.mk (RingHom.ker ev) (MvPolynomial.X i))), ?_⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, RingHom.algebraMap_toAlgebra,
    IsFractionRing.lift_algebraMap, RingHom.kerLift_mk]
  simp [ev]

theorem fibrePoly_map_ringHom {R S : Type*} [Field R] [Field S] (φ : R →+* S)
    (Φ : Polynomial (Polynomial ℤ)) (a : R) :
    fibrePoly Φ (φ a) = (fibrePoly Φ a).map φ := by
  have hcomp : Polynomial.eval₂RingHom (Int.castRingHom S) (φ a) =
      φ.comp (Polynomial.eval₂RingHom (Int.castRingHom R) a) := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · simp
    · simp
  rw [fibrePoly, fibrePoly, hcomp, ← Polynomial.map_map]

def ConclT {F : Type*} [Field F] [DecidableEq F] (X : WeierstrassCurve F) [X.IsElliptic]
    {ι : Type*} [Fintype ι] (Q : ι → X.toAffine.Point) (n : ℕ)
    (hΔ : ∀ i, (X.veluQuotient (X.oddOrderSummingSet (Q i) n)).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) : Prop :=
  fibrePoly data.Φ X.j =
    ∏ i, (Polynomial.X - C (@WeierstrassCurve.j F _
      (X.veluQuotient (X.oddOrderSummingSet (Q i) n)) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩))

theorem j_congr {F : Type*} [Field F] {A B : WeierstrassCurve F} (h : A = B)
    (hA : A.IsElliptic) (hB : B.IsElliptic) :
    @WeierstrassCurve.j F _ A hA = @WeierstrassCurve.j F _ B hB := by
  subst h
  rfl

section Transport

variable {R S : Type*} [Field R] [Field S] [DecidableEq R] [DecidableEq S] (φ : R →+* S)
  (V : WeierstrassCurve R) [V.IsElliptic]

theorem veluQuotient_oddOrderSummingSet_mapPoint (Q : V.toAffine.Point) (n : ℕ) :
    (V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (mapPoint φ V Q) n) =
      (V.veluQuotient (V.oddOrderSummingSet Q n)).map φ := by
  rw [oddOrderSummingSet_mapPoint φ V Q n,
    veluQuotient_map φ V _ (Function.Injective.prodMap φ.injective φ.injective).injOn]

theorem veluQuotient_mapPoint_Δ_ne_zero_iff (Q : V.toAffine.Point) (n : ℕ) :
    ((V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (mapPoint φ V Q) n)).Δ ≠ 0 ↔
      (V.veluQuotient (V.oddOrderSummingSet Q n)).Δ ≠ 0 := by
  rw [veluQuotient_oddOrderSummingSet_mapPoint, WeierstrassCurve.map_Δ, map_ne_zero_iff φ φ.injective]

theorem conclT_map_iff {ι : Type*} [Fintype ι] (Q : ι → V.toAffine.Point) (n : ℕ)
    (hΔ : ∀ i, (V.veluQuotient (V.oddOrderSummingSet (Q i) n)).Δ ≠ 0)
    (hΔ' : ∀ i, ((V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (mapPoint φ V (Q i)) n)).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) :
    ConclT (V.map φ) (fun i => mapPoint φ V (Q i)) n hΔ' data ↔ ConclT V Q n hΔ data := by
  unfold ConclT
  have hj : ∀ i, @WeierstrassCurve.j S _
      ((V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (mapPoint φ V (Q i)) n))
        ⟨isUnit_iff_ne_zero.mpr (hΔ' i)⟩
      = φ (@WeierstrassCurve.j R _ (V.veluQuotient (V.oddOrderSummingSet (Q i) n))
          ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩) := by
    intro i
    haveI : (V.veluQuotient (V.oddOrderSummingSet (Q i) n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩
    rw [j_congr (veluQuotient_oddOrderSummingSet_mapPoint φ V (Q i) n) ⟨isUnit_iff_ne_zero.mpr (hΔ' i)⟩
      inferInstance, WeierstrassCurve.map_j]
  have hrhs : (∏ i, (Polynomial.X - C (@WeierstrassCurve.j S _
      ((V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (mapPoint φ V (Q i)) n))
        ⟨isUnit_iff_ne_zero.mpr (hΔ' i)⟩)))
      = (∏ i, (Polynomial.X - C (@WeierstrassCurve.j R _
          (V.veluQuotient (V.oddOrderSummingSet (Q i) n)) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩))).map φ := by
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hj i]
  rw [WeierstrassCurve.map_j, fibrePoly_map_ringHom, hrhs]
  exact (Polynomial.map_injective φ φ.injective).eq_iff

end Transport

section EmbedHahn
open Cardinal

theorem aleph0_lt_mk_hahn : ℵ₀ < #(HahnSeries ℚ (AlgebraicClosure ℚ)) := by
  classical
  let f : Set ℕ → HahnSeries ℚ (AlgebraicClosure ℚ) := fun S =>
    HahnSeries.ofPowerSeries ℚ (AlgebraicClosure ℚ) (PowerSeries.mk fun n => if n ∈ S then 1 else 0)
  have hf : Function.Injective f := by
    intro S T h
    have h' := HahnSeries.ofPowerSeries_injective h
    ext n
    have hn := congrArg (PowerSeries.coeff n) h'
    simp only [PowerSeries.coeff_mk] at hn
    by_cases hS : n ∈ S <;> by_cases hT : n ∈ T <;> simp_all
  calc ℵ₀ = #ℕ := Cardinal.mk_nat.symm
    _ < 2 ^ #ℕ := Cardinal.cantor _
    _ = #(Set ℕ) := (Cardinal.mk_set).symm
    _ ≤ #(HahnSeries ℚ (AlgebraicClosure ℚ)) := Cardinal.mk_le_of_injective hf

theorem nonempty_ringHom_hahn (L : Type) [Field L] [CharZero L] [Countable L] :
    Nonempty (L →+* HahnSeries ℚ (AlgebraicClosure ℚ)) := by
  classical
  haveI : IsAlgClosed (HahnSeries ℚ (AlgebraicClosure ℚ)) := HahnSeries.isAlgClosed_rat

  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ L
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ (HahnSeries ℚ (AlgebraicClosure ℚ))

  have hK : #(HahnSeries ℚ (AlgebraicClosure ℚ)) = #t := by
    simpa using IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht
      Cardinal.mk_le_aleph0 aleph0_lt_mk_hahn
  have hst : #s ≤ #t := by
    rw [← hK]
    exact (Cardinal.mk_le_aleph0.trans aleph0_lt_mk_hahn.le)
  obtain ⟨e⟩ : Nonempty (s ↪ t) := (Cardinal.le_def _ _).mp hst

  let w : s → HahnSeries ℚ (AlgebraicClosure ℚ) := fun x => ((e x : t) : HahnSeries ℚ (AlgebraicClosure ℚ))
  have hw : AlgebraicIndependent ℚ w := ht.1.comp _ e.injective

  let A : Subalgebra ℚ L := Algebra.adjoin ℚ (Set.range ((↑) : s → L))
  let A' : Subalgebra ℚ (HahnSeries ℚ (AlgebraicClosure ℚ)) := Algebra.adjoin ℚ (Set.range w)
  let ψ₁ : A →+* HahnSeries ℚ (AlgebraicClosure ℚ) :=
    (algebraMap A' (HahnSeries ℚ (AlgebraicClosure ℚ))).comp
      (hw.aevalEquiv.toRingEquiv.toRingHom.comp hs.1.aevalEquiv.symm.toRingEquiv.toRingHom)
  have hψ₁ : Function.Injective ψ₁ := by
    intro a b hab
    have h1 : ((hw.aevalEquiv (hs.1.aevalEquiv.symm a) : A') : HahnSeries ℚ (AlgebraicClosure ℚ))
        = (hw.aevalEquiv (hs.1.aevalEquiv.symm b) : A') := hab
    exact hs.1.aevalEquiv.symm.injective (hw.aevalEquiv.injective (Subtype.val_injective h1))

  haveI : Algebra.IsAlgebraic A L := hs.isAlgebraic
  letI : Algebra A (HahnSeries ℚ (AlgebraicClosure ℚ)) := ψ₁.toAlgebra
  haveI : Module.IsTorsionFree A (HahnSeries ℚ (AlgebraicClosure ℚ)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [RingHom.algebraMap_toAlgebra]; exact hψ₁)
  haveI : Module.IsTorsionFree A L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Subtype.val_injective
  exact ⟨(IsAlgClosed.lift : L →ₐ[A] HahnSeries ℚ (AlgebraicClosure ℚ)).toRingHom⟩

theorem exists_cover_hahn {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] {m : ℕ} (g : Fin m → F) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : IsAlgClosed K₀) (φ : K₀ →+* F)
      (_ : K₀ →+* HahnSeries ℚ (AlgebraicClosure ℚ)), ∀ i, g i ∈ Set.range φ := by
  classical
  let ev : MvPolynomial (Fin m) ℤ →+* F := MvPolynomial.eval₂Hom (Int.castRingHom F) g
  haveI : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  let D : Type := MvPolynomial (Fin m) ℤ ⧸ RingHom.ker ev
  let ψ₁ : D →+* F := RingHom.kerLift ev
  have hψ₁ : Function.Injective ψ₁ := RingHom.kerLift_injective ev
  let L : Type := FractionRing D
  let ψ₂ : L →+* F := IsFractionRing.lift hψ₁
  let K₀ : Type := AlgebraicClosure L
  letI : Algebra L F := ψ₂.toAlgebra
  haveI : Module.IsTorsionFree L F :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [RingHom.algebraMap_toAlgebra]; exact ψ₂.injective)
  let ψ₃ : K₀ →ₐ[L] F := IsAlgClosed.lift

  haveI : CharZero L := ψ₂.charZero
  haveI : Countable (MvPolynomial (Fin m) ℤ) := Cardinal.mk_le_aleph0_iff.mp
    ((MvPolynomial.cardinalMk_le_max (σ := Fin m) (R := ℤ)).trans
      (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))
  haveI : Countable D := Quotient.countable
  haveI : Countable L := Cardinal.mk_le_aleph0_iff.mp
    ((Localization.cardinalMk_le (S := nonZeroDivisors D)).trans Cardinal.mk_le_aleph0)
  obtain ⟨χ⟩ := nonempty_ringHom_hahn L
  letI alg𝕂 : Algebra L (HahnSeries ℚ (AlgebraicClosure ℚ)) := χ.toAlgebra
  haveI : Module.IsTorsionFree L (HahnSeries ℚ (AlgebraicClosure ℚ)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [RingHom.algebraMap_toAlgebra]; exact χ.injective)
  haveI : IsAlgClosed (HahnSeries ℚ (AlgebraicClosure ℚ)) := HahnSeries.isAlgClosed_rat
  let ψ₄ : K₀ →ₐ[L] HahnSeries ℚ (AlgebraicClosure ℚ) := IsAlgClosed.lift
  refine ⟨K₀, inferInstance, inferInstance, ψ₃.toRingHom, ψ₄.toRingHom, fun i => ?_⟩
  refine ⟨algebraMap L K₀ (algebraMap D L (Ideal.Quotient.mk (RingHom.ker ev) (MvPolynomial.X i))), ?_⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, RingHom.algebraMap_toAlgebra,
    IsFractionRing.lift_algebraMap, RingHom.kerLift_mk]
  simp [ev]

end EmbedHahn

section Assembly

theorem transcendental_ringHom_iff {R S : Type*} [Field R] [Field S] [Algebra ℚ R] [Algebra ℚ S]
    (φ : R →+* S) (a : R) : Transcendental ℚ (φ a) ↔ Transcendental ℚ a := by
  have key : IsAlgebraic ℚ ((φ.toRatAlgHom : R →ₐ[ℚ] S) a) ↔ IsAlgebraic ℚ a :=
    isAlgebraic_algHom_iff (φ.toRatAlgHom) φ.injective
  exact not_congr (by simpa using key)

theorem aux (K₀ : Type*) [Field K₀] [IsAlgClosed K₀]
    (ψ : K₀ →+* HahnSeries ℚ (AlgebraicClosure ℚ))
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    (φ : K₀ →+* F) (V : WeierstrassCurve K₀)
    {ι : Type*} [Fintype ι] (n : ℕ) [Fact (2 * n + 1).Prime] (hn2 : 2 * n + 1 ≠ 2)
    (hι : Fintype.card ι = 2 * n + 1 + 1)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) :
    ∀ (Q : ι → (V.map φ).toAffine.Point),
      (∀ i, (Q i).coordsOrZero.1 ∈ Set.range φ ∧ (Q i).coordsOrZero.2 ∈ Set.range φ) →
      ∀ (hE : (V.map φ).IsElliptic), Transcendental ℚ (@WeierstrassCurve.j F _ (V.map φ) hE) →
      (∀ i, addOrderOf (Q i) = 2 * n + 1) →
      (Function.Injective fun i => AddSubgroup.zmultiples (Q i)) →
      ∀ (hΔ : ∀ i, ((V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (Q i) n)).Δ ≠ 0),
      @ConclT F _ _ (V.map φ) hE ι _ Q n hΔ data := by
  intro Q hQr hE ht hord hinjQ hΔ
  haveI : DecidableEq K₀ := Classical.decEq _
  haveI : CharZero K₀ := φ.charZero

  have hdesc : ∀ i, ∃ P₀ : V.toAffine.Point, mapPoint φ V P₀ = Q i := by
    intro i
    obtain ⟨hx, hy⟩ := hQr i
    rcases hQi : Q i with _ | ⟨x, y, h⟩
    · exact ⟨0, rfl⟩
    · rw [hQi] at hx hy
      obtain ⟨x₀, rfl⟩ := hx
      obtain ⟨y₀, rfl⟩ := hy
      exact ⟨Affine.Point.some x₀ y₀
        ((Affine.map_nonsingular (W := V.toAffine) (f := φ) φ.injective x₀ y₀).mp h), rfl⟩
  choose Q₀ hQ₀ using hdesc
  have hQfun : Q = fun i => mapPoint φ V (Q₀ i) := funext fun i => (hQ₀ i).symm
  subst hQfun

  have hV : V.IsElliptic := by
    refine ⟨isUnit_iff_ne_zero.mpr fun h0 => ?_⟩
    have h1 : (V.map φ).Δ = 0 := by rw [WeierstrassCurve.map_Δ, h0, map_zero]
    exact (isUnit_iff_ne_zero.mp (@WeierstrassCurve.isUnit_Δ _ _ (V.map φ) hE)) h1
  have ht₀ : Transcendental ℚ V.j := by
    rw [WeierstrassCurve.map_j] at ht
    exact (transcendental_ringHom_iff φ V.j).mp ht
  have hord₀ : ∀ i, addOrderOf (Q₀ i) = 2 * n + 1 := fun i => by
    rw [← addOrderOf_mapPoint φ V (Q₀ i)]; exact hord i
  have hinj₀ : Function.Injective fun i => AddSubgroup.zmultiples (Q₀ i) := by
    intro i i' h
    apply hinjQ
    simp only at h ⊢
    rw [← AddMonoidHom.map_zmultiples, ← AddMonoidHom.map_zmultiples, h]
  have hΔ₀ : ∀ i, (V.veluQuotient (V.oddOrderSummingSet (Q₀ i) n)).Δ ≠ 0 := fun i =>
    (veluQuotient_mapPoint_Δ_ne_zero_iff φ V (Q₀ i) n).mp (hΔ i)

  haveI : DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ)) := Classical.decEq _
  have hΔ₁ : ∀ i, ((V.map ψ).veluQuotient ((V.map ψ).oddOrderSummingSet (mapPoint ψ V (Q₀ i)) n)).Δ ≠ 0 :=
    fun i => (veluQuotient_mapPoint_Δ_ne_zero_iff ψ V (Q₀ i) n).mpr (hΔ₀ i)
  have ht₁ : Transcendental ℚ (V.map ψ).j := by
    rw [WeierstrassCurve.map_j]; exact (transcendental_ringHom_iff ψ V.j).mpr ht₀
  have hord₁ : ∀ i, addOrderOf (mapPoint ψ V (Q₀ i)) = 2 * n + 1 := fun i => by
    rw [addOrderOf_mapPoint]; exact hord₀ i
  have hinj₁ : Function.Injective fun i => AddSubgroup.zmultiples (mapPoint ψ V (Q₀ i)) := by
    intro i i' h
    apply hinj₀
    simp only at h ⊢
    rw [← AddMonoidHom.map_zmultiples, ← AddMonoidHom.map_zmultiples] at h
    exact AddSubgroup.map_injective (mapPoint_injective ψ V) h
  have hn : (2 * n + 1) / 2 = n := by omega

  have G0 : ∀ (hΔm : ∀ i, ((V.map ψ).veluQuotient
        ((V.map ψ).oddOrderSummingSet (mapPoint ψ V (Q₀ i)) ((2 * n + 1) / 2))).Δ ≠ 0),
      fibrePoly data.Φ (V.map ψ).j =
        ∏ i, (Polynomial.X - C (@WeierstrassCurve.j _ _
          ((V.map ψ).veluQuotient ((V.map ψ).oddOrderSummingSet (mapPoint ψ V (Q₀ i)) ((2 * n + 1) / 2)))
          ⟨isUnit_iff_ne_zero.mpr (hΔm i)⟩)) :=
    fun hΔm => ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental
      hn2 data (V.map ψ) ht₁ hι (fun i => mapPoint ψ V (Q₀ i)) hord₁ hinj₁ hΔm
  rw [hn] at G0
  have G' : ConclT (V.map ψ) (fun i => mapPoint ψ V (Q₀ i)) n hΔ₁ data := G0 hΔ₁

  have H₀ : ConclT V Q₀ n hΔ₀ data := (conclT_map_iff ψ V Q₀ n hΔ₀ hΔ₁ data).mp G'
  exact (conclT_map_iff φ V Q₀ n hΔ₀ hΔ data).mpr H₀

theorem main {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] [CharZero K]
    (n : ℕ) [Fact (2 * n + 1).Prime] (hn2 : 2 * n + 1 ≠ 2)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) (W : WeierstrassCurve K) [W.IsElliptic]
    (ht : Transcendental ℚ W.j)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 2 * n + 1 + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = 2 * n + 1)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) n)).Δ ≠ 0) :
    ConclT W Q n hΔ data := by
  classical

  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  let g : Fin (5 + 2 * Fintype.card ι) → K := fun k =>
    Fin.addCases (![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆])
      (fun k' : Fin (2 * Fintype.card ι) =>
        if k'.val % 2 = 0 then (Q (e.symm ⟨k'.val / 2, by omega⟩)).coordsOrZero.1
        else (Q (e.symm ⟨k'.val / 2, by omega⟩)).coordsOrZero.2) k
  obtain ⟨K₀, _, _, φ, ψ, hg⟩ := exists_cover_hahn g
  obtain ⟨b₁, hb₁⟩ := hg (Fin.castAdd _ 0)
  obtain ⟨b₂, hb₂⟩ := hg (Fin.castAdd _ 1)
  obtain ⟨b₃, hb₃⟩ := hg (Fin.castAdd _ 2)
  obtain ⟨b₄, hb₄⟩ := hg (Fin.castAdd _ 3)
  obtain ⟨b₆, hb₆⟩ := hg (Fin.castAdd _ 4)
  have hcoord : ∀ i, (Q i).coordsOrZero.1 ∈ Set.range φ ∧ (Q i).coordsOrZero.2 ∈ Set.range φ := by
    intro i
    constructor
    · have := hg (Fin.natAdd 5 ⟨2 * (e i).val, by omega⟩)
      simpa [g, Fin.addCases, Nat.mul_mod_right, Nat.mul_div_right] using this
    · have := hg (Fin.natAdd 5 ⟨2 * (e i).val + 1, by omega⟩)
      simpa [g, Fin.addCases, Nat.mul_add_mod, Nat.mul_add_div] using this
  let V : WeierstrassCurve K₀ := ⟨b₁, b₂, b₃, b₄, b₆⟩
  have hW : V.map φ = W := by
    ext
    · simpa [g, Fin.addCases] using hb₁
    · simpa [g, Fin.addCases] using hb₂
    · simpa [g, Fin.addCases] using hb₃
    · simpa [g, Fin.addCases] using hb₄
    · simpa [g, Fin.addCases] using hb₆
  have key : ∀ (Q' : ι → W.toAffine.Point),
      (∀ i, (Q' i).coordsOrZero.1 ∈ Set.range φ ∧ (Q' i).coordsOrZero.2 ∈ Set.range φ) →
      ∀ (hE : W.IsElliptic), Transcendental ℚ (@WeierstrassCurve.j K _ W hE) →
      (∀ i, addOrderOf (Q' i) = 2 * n + 1) →
      (Function.Injective fun i => AddSubgroup.zmultiples (Q' i)) →
      ∀ (hΔ' : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q' i) n)).Δ ≠ 0),
      @ConclT K _ _ W hE ι _ Q' n hΔ' data := by
    rw [← hW]
    exact aux K₀ ψ φ V n hn2 hι data
  exact key Q hcoord inferInstance ht hQ hQinj hΔ

end Assembly

end TDescent

end

open Polynomial ModularCurve WeierstrassCurve WeierstrassCurve.Affine in
theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] [CharZero K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve K) [W.IsElliptic]
    (ht : Transcendental ℚ W.j)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _
        (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  have hℓP : ℓ.Prime := Fact.out
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = 2 * n + 1 := by
    rcases hℓP.eq_two_or_odd' with h | h
    · exact absurd h hℓ2
    · exact h
  have hn : (2 * n + 1) / 2 = n := by omega
  revert hΔ
  rw [hn]
  intro hΔ
  exact TDescent.main n hℓ2 data W ht hι Q hQ hQinj hΔ

end S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed (solution)

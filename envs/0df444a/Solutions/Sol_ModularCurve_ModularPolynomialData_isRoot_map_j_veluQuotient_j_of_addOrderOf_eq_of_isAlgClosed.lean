-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/f0fd2a89-161e-5822-83be-fa5b4334e79f

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Theorems.Thm_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
import Theorems.Thm_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples
import Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix"
p2m_attr_erase "simp" "ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"

set_option autoImplicit false

namespace N4Glue

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem isRoot_veluQuotient_j_type0
    (K : Type) [Field K] [DecidableEq K] [CharZero K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) :
    haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K) W.j)).IsRoot
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j := by
  haveI hE' : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩

  haveI : W.toAffine.IsElliptic := ‹W.IsElliptic›
  haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.IsElliptic := hE'
  haveI : IsDedekindDomain W.toAffine.CoordinateRing := CoordinateRing.isDedekindDomain W
  haveI : HasPrincipalDivisors K W.toAffine.FunctionField := hasPrincipalDivisors_functionField W.toAffine
  obtain ⟨g, hgc, hga⟩ :=
    exists_genusOnePlaceGate_isCentred_and_abelTheorem (F := K) (W := W.toAffine)
  letI := g
  haveI := hgc
  haveI := hga
  haveI : IsDedekindDomain (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.CoordinateRing :=
    CoordinateRing.isDedekindDomain (W.veluQuotient (W.oddOrderSummingSet Q n))
  haveI : HasPrincipalDivisors K (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField :=
    hasPrincipalDivisors_functionField (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine
  obtain ⟨g', hgc', hga'⟩ :=
    exists_genusOnePlaceGate_isCentred_and_abelTheorem (F := K)
      (W := (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine)
  letI := g'
  haveI := hgc'
  haveI := hga'

  obtain ⟨ι, hι, hfin, hdeg, hker⟩ :=
    WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples
      (W := W) (Q := Q) (n := n) hQ hΔ

  haveI : CharZero (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField :=
    charZero_of_injective_algebraMap
      (algebraMap K (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField).injective
  have hsep : SeparableAlong K ι := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI : Module.Finite (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField
        W.toAffine.FunctionField := hfin
    show Algebra.IsSeparable _ _
    infer_instance
  have hN : NormFormulaAlong K ι hfin := AlgebraicCurve.normFormulaAlong ι hfin hsep
  have hkerQ := hker hN
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  have hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker := by
    rw [hkerQ]; infer_instance
  have hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = 2 * n + 1 := by
    rw [hkerQ, Nat.card_zmultiples, hQ]
  exact WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
    K W.toAffine (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine ι hι hfin hN (2 * n + 1)
    hcyc hcard data

end N4Glue

namespace ModularCurve
p2m_export "ModularCurve" "ModularPolynomialData"
namespace N4
p2m_open "ModularCurve"
open WeierstrassCurve WeierstrassCurve.Affine in

theorem isRoot_map_j_veluQuotient_j_of_type0
    (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) :
    haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K) W.j)).IsRoot
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j :=
  N4Glue.isRoot_veluQuotient_j_type0 K W n Q hQ hΔ data
end ModularCurve.N4

open WeierstrassCurve WeierstrassCurve.Affine

namespace N4Descent

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

def Concl {F : Type*} [Field F] [DecidableEq F] (X : WeierstrassCurve F) [X.IsElliptic]
    (Q : X.toAffine.Point) (n : ℕ) (hΔ : (X.veluQuotient (X.oddOrderSummingSet Q n)).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) : Prop :=
  haveI : (X.veluQuotient (X.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) X.j)).IsRoot
    (X.veluQuotient (X.oddOrderSummingSet Q n)).j

theorem j_congr {F : Type*} [Field F] {A B : WeierstrassCurve F} (h : A = B)
    (hA : A.IsElliptic) (hB : B.IsElliptic) : @WeierstrassCurve.j F _ A hA = @WeierstrassCurve.j F _ B hB := by
  subst h
  rfl

theorem aux (K₀ : Type) [Field K₀] [IsAlgClosed K₀]
    {F : Type uF} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    (φ : K₀ →+* F) (V : WeierstrassCurve K₀) :
    ∀ (Q : (V.map φ).toAffine.Point), Q.coordsOrZero.1 ∈ Set.range φ → Q.coordsOrZero.2 ∈ Set.range φ →
      ∀ (hE : (V.map φ).IsElliptic) (n : ℕ), addOrderOf Q = 2 * n + 1 →
      ∀ (hΔ : ((V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet Q n)).Δ ≠ 0)
        (data : ModularCurve.ModularPolynomialData (2 * n + 1)),
      @Concl F _ _ (V.map φ) hE Q n hΔ data := by
  intro Q hx hy hE n hQ hΔ data
  haveI : DecidableEq K₀ := Classical.decEq _
  haveI : CharZero K₀ := φ.charZero

  obtain ⟨Q₀, rfl⟩ : ∃ Q₀ : V.toAffine.Point, mapPoint φ V Q₀ = Q := by
    rcases Q with _ | ⟨x, y, h⟩
    · exact ⟨0, rfl⟩
    · obtain ⟨x₀, rfl⟩ := hx
      obtain ⟨y₀, rfl⟩ := hy
      exact ⟨Affine.Point.some x₀ y₀ ((Affine.map_nonsingular (W := V.toAffine) (f := φ) φ.injective x₀ y₀).mp h),
        rfl⟩

  have hV : V.IsElliptic := by
    refine ⟨isUnit_iff_ne_zero.mpr fun h0 => ?_⟩
    have h1 : (V.map φ).Δ = 0 := by rw [WeierstrassCurve.map_Δ, h0, map_zero]
    exact (isUnit_iff_ne_zero.mp (WeierstrassCurve.isUnit_Δ (W := V.map φ))) h1
  have hQ₀ : addOrderOf Q₀ = 2 * n + 1 := by rwa [addOrderOf_mapPoint] at hQ
  have hinj : Set.InjOn (Prod.map φ φ) ↑(V.oddOrderSummingSet Q₀ n) :=
    (Function.Injective.prodMap φ.injective φ.injective).injOn
  have hS : (V.map φ).oddOrderSummingSet (mapPoint φ V Q₀) n =
      (V.oddOrderSummingSet Q₀ n).image (Prod.map φ φ) := oddOrderSummingSet_mapPoint φ V Q₀ n
  have hcurve : (V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (mapPoint φ V Q₀) n) =
      (V.veluQuotient (V.oddOrderSummingSet Q₀ n)).map φ := by
    rw [hS, veluQuotient_map φ V _ hinj]
  have hΔ₀ : (V.veluQuotient (V.oddOrderSummingSet Q₀ n)).Δ ≠ 0 := by
    intro h0
    apply hΔ
    rw [hcurve, WeierstrassCurve.map_Δ, h0, map_zero]

  have key := ModularCurve.N4.isRoot_map_j_veluQuotient_j_of_type0 K₀ V n Q₀ hQ₀ hΔ₀ data

  haveI hE₀' : (V.veluQuotient (V.oddOrderSummingSet Q₀ n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ₀⟩
  have hj1 : (V.map φ).j = φ V.j := V.map_j φ
  have hj2 : @WeierstrassCurve.j F _ ((V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (mapPoint φ V Q₀) n))
      ⟨isUnit_iff_ne_zero.mpr hΔ⟩ = φ (V.veluQuotient (V.oddOrderSummingSet Q₀ n)).j := by
    rw [j_congr hcurve ⟨isUnit_iff_ne_zero.mpr hΔ⟩ inferInstance, WeierstrassCurve.map_j]
  unfold Concl
  rw [hj1, hj2, isRoot_map_iff φ φ.injective]
  exact key

theorem main {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) :
    haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) W.j)).IsRoot
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j := by
  obtain ⟨K₀, _, _, φ, hg⟩ :=
    exists_cover ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆, Q.coordsOrZero.1, Q.coordsOrZero.2]
  obtain ⟨b₁, hb₁⟩ := hg 0
  obtain ⟨b₂, hb₂⟩ := hg 1
  obtain ⟨b₃, hb₃⟩ := hg 2
  obtain ⟨b₄, hb₄⟩ := hg 3
  obtain ⟨b₆, hb₆⟩ := hg 4
  have hx : Q.coordsOrZero.1 ∈ Set.range φ := by simpa using hg 5
  have hy : Q.coordsOrZero.2 ∈ Set.range φ := by simpa using hg 6
  let V : WeierstrassCurve K₀ := ⟨b₁, b₂, b₃, b₄, b₆⟩
  have hW : V.map φ = W := by
    ext
    · simpa using hb₁
    · simpa using hb₂
    · simpa using hb₃
    · simpa using hb₄
    · simpa using hb₆
  have key : ∀ (Q' : W.toAffine.Point), Q'.coordsOrZero.1 ∈ Set.range φ → Q'.coordsOrZero.2 ∈ Set.range φ →
      ∀ (hE : W.IsElliptic) (n' : ℕ), addOrderOf Q' = 2 * n' + 1 →
      ∀ (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q' n')).Δ ≠ 0)
        (data' : ModularCurve.ModularPolynomialData (2 * n' + 1)),
      @Concl F _ _ W hE Q' n' hΔ' data' := by
    rw [← hW]
    exact aux K₀ φ V
  exact key Q hx hy inferInstance n hQ hΔ data

end N4Descent

theorem solution {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) :
    haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) W.j)).IsRoot
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j :=
  N4Descent.main W n Q hQ hΔ data

end S_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq_of_isAlgClosed (solution)

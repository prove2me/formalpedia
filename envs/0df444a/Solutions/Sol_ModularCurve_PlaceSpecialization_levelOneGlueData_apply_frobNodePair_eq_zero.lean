-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.levelOneGlueData_apply_frobNodePair_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a2b98b8c-072e-5f6a-b8df-14215aebb351

import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_levelOneGlueData_apply_frobNodePair_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (S₀ : Finset k) (hS₀ : ∀ a ∈ S₀, a ∈ ssJSet q k)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (a : k) (ha : a ∈ S₀) :
    (P.levelOneGlueData (nodePairsOf q S₀) D).1 (frobNodePair q a).1 = 0 ∧
      (P.levelOneGlueData (nodePairsOf q S₀) D).2.1 (frobNodePair q a).2 = 0 := by
  classical

  have hφ : ∀ b : k, frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k b)
      = charLGeomPlaceOfPoint k (b ^ q) := fun b => by
    rw [← ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr]
    exact ModularCurve.arithFrobC_smul_charLGeomPlaceOfPoint q b

  have ha2 : (a ^ q) ^ q = a := by
    rw [← pow_mul, ← sq]
    exact ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q (hS₀ a ha)
  have hfix1 : frobOnPlacesGeomLevel k 1 data hKr
      (frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a)) = charLGeomPlaceOfPoint k a := by
    rw [hφ, hφ, ha2]
  have hfix2 : frobOnPlacesGeomLevel k 1 data hKr
      (frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k (a ^ q)))
        = charLGeomPlaceOfPoint k (a ^ q) := by
    rw [hφ, hφ, ha2]
  constructor
  · show (Finsupp.mapDomain P.redFst (P.fstPart D)) (charLGeomPlaceOfPoint k a) = 0
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun W hW => ?_
    rw [Finsupp.single_apply, if_neg]
    intro hred
    have hne : (P.fstPart D) W ≠ 0 := Finsupp.mem_support_iff.mp hW
    have h1 : P.IsStrictTypeOne W := by
      by_contra hc
      apply hne
      show (Finsupp.filter P.IsStrictTypeOne D) W = 0
      rw [Finsupp.filter_apply, if_neg hc]
    exact h1.2 (by rw [hred]; exact hfix1)
  · show (Finsupp.mapDomain P.redSnd (P.sndPart D)) (charLGeomPlaceOfPoint k (a ^ q)) = 0
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun W hW => ?_
    rw [Finsupp.single_apply, if_neg]
    intro hred
    have hne : (P.sndPart D) W ≠ 0 := Finsupp.mem_support_iff.mp hW
    have h2 : P.IsStrictTypeTwo W := by
      by_contra hc
      apply hne
      show (Finsupp.filter P.IsStrictTypeTwo D) W = 0
      rw [Finsupp.filter_apply, if_neg hc]
    exact h2.2 (by rw [hred]; exact hfix2)

end S_ModularCurve_PlaceSpecialization_levelOneGlueData_apply_frobNodePair_eq_zero
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_levelOneGlueData_apply_frobNodePair_eq_zero (solution)

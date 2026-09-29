-- Prove2me | solution 1 for ModularCurve.LevelP.isLevelPStructure_borelDataPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3ea0c9a9-f8a8-5bd3-b0ba-5791227de557

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps
import Theorems.Thm_WeierstrassCurve_eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelP_isLevelPStructure_borelDataPrime
p2m_attr_erase "instance" "WeierstrassCurve.Generic.isElliptic_curve WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

noncomputable section

open Polynomial WeierstrassCurve

namespace ModularCurve
p2m_export "ModularCurve" "indepElt indepElt_map IsLevelPStructure LevelP.TorsionPointRing LevelP.UnivBasisRing LevelP.equation_borelQ LevelP.BorelRing LevelP.borelCurve LevelP.borelData'"
namespace LevelP
p2m_export "ModularCurve.LevelP" "preΨ_eval_map equation_map TorsionPointRing TorsionPointRing.ofBase torsionPtCurve equation_torsionPt preΨ_torsionPt UnivBasisRing univCurveT isLevelPStructure_univData isUnit_Δ_univCurveT isUnit_natCast_univBasisRing borelX borelQuadratic borelQY borelQCurve equation_borelQ BorelPRing BorelPRing.xP BorelPRing.xQ borelPCurve borelPCurve_eq BorelRing borelCurve borelCurve_eq_map_borelPCurve borelData' isUnit_algebraMap_borelDenom"
namespace BorelProof
p2m_open "ModularCurve.LevelP ModularCurve"

variable (p : ℕ) [Fact p.Prime]

theorem not_dvd_of_le {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) : ¬ (p : ℤ) ∣ (a : ℤ) := by
  intro h
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h' : p ∣ a := Int.natCast_dvd_natCast.mp h
  have hle : p ≤ a := Nat.le_of_dvd ha h'
  omega

theorem eval_preΨ_borelX (hp2 : p ≠ 2) {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) :
    ((univCurveT p).preΨ p).eval (borelX p a) = 0 :=
  ((univCurveT p).eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero hp2
    ((isUnit_natCast_univBasisRing p).mul (isUnit_Δ_univCurveT p))
    (isLevelPStructure_univData p).preΨ_Q (not_dvd_of_le p ha ha')).2

theorem isLevelPStructure (hp2 : p ≠ 2) {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) :
    IsLevelPStructure (borelCurve p a) p (borelData' p a) := by
  have hΨ := eval_preΨ_borelX p hp2 ha ha'
  rw [borelCurve_eq_map_borelPCurve]
  exact
  { equation_P := equation_map _ (equation_torsionPt (borelQCurve p a) p)
    equation_Q := by
      refine equation_map _ ?_
      show (torsionPtCurve (borelQCurve p a) p).toAffine.Equation
        (TorsionPointRing.ofBase (borelQCurve p a) p (AdjoinRoot.of (borelQuadratic p a) (borelX p a)))
        (TorsionPointRing.ofBase (borelQCurve p a) p (borelQY p a))
      exact equation_map _ (equation_borelQ p a)
    preΨ_P := by
      show (((borelPCurve p a).map (algebraMap (BorelPRing p a) (BorelRing p a))).preΨ p).eval
        (algebraMap _ _ (BorelPRing.xP p a)) = 0
      rw [preΨ_eval_map, BorelPRing.xP, preΨ_torsionPt, map_zero]
    preΨ_Q := by
      show (((borelPCurve p a).map (algebraMap (BorelPRing p a) (BorelRing p a))).preΨ p).eval
        (algebraMap _ _ (BorelPRing.xQ p a)) = 0
      rw [preΨ_eval_map, BorelPRing.xQ, borelPCurve_eq, preΨ_eval_map, hΨ, map_zero, map_zero]
    isUnit_indepElt_PQ := by
      show IsUnit (indepElt ((borelPCurve p a).map (algebraMap (BorelPRing p a) (BorelRing p a))) p
        (algebraMap _ _ (BorelPRing.xP p a)) (algebraMap _ _ (BorelPRing.xQ p a)))
      rw [indepElt_map]
      have h : IsUnit (algebraMap (BorelPRing p a) (BorelRing p a)
          (indepElt (borelPCurve p a) p (BorelPRing.xP p a) (BorelPRing.xQ p a) *
            indepElt (borelPCurve p a) p (BorelPRing.xQ p a) (BorelPRing.xP p a))) :=
        isUnit_algebraMap_borelDenom p a
      rw [map_mul] at h
      exact isUnit_of_mul_isUnit_left h
    isUnit_indepElt_QP := by
      show IsUnit (indepElt ((borelPCurve p a).map (algebraMap (BorelPRing p a) (BorelRing p a))) p
        (algebraMap _ _ (BorelPRing.xQ p a)) (algebraMap _ _ (BorelPRing.xP p a)))
      rw [indepElt_map]
      have h : IsUnit (algebraMap (BorelPRing p a) (BorelRing p a)
          (indepElt (borelPCurve p a) p (BorelPRing.xP p a) (BorelPRing.xQ p a) *
            indepElt (borelPCurve p a) p (BorelPRing.xQ p a) (BorelPRing.xP p a))) :=
        isUnit_algebraMap_borelDenom p a
      rw [map_mul] at h
      exact isUnit_of_mul_isUnit_right h }

end ModularCurve.LevelP.BorelProof

theorem solution (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) :
    ModularCurve.IsLevelPStructure (ModularCurve.LevelP.borelCurve p a) p
      (ModularCurve.LevelP.borelData' p a) :=
  ModularCurve.LevelP.BorelProof.isLevelPStructure p hp2 ha ha'

end
end S_ModularCurve_LevelP_isLevelPStructure_borelDataPrime
end P2MW
export P2MW.S_ModularCurve_LevelP_isLevelPStructure_borelDataPrime (solution)

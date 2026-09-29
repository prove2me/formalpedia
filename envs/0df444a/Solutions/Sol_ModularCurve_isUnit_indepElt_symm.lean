-- Prove2me | solution 1 for ModularCurve.isUnit_indepElt_symm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/2376c364-8b6f-51c9-88b4-32ce7e7c94d3

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isUnit_indepElt_symm
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

p2m_open "ModularCurve P2MW.S_ModularCurve_isUnit_indepElt_symm.ModularCurve WeierstrassCurve"

namespace ModularCurve
p2m_export "ModularCurve" "indepElt indepElt_map indepElt_eq_zero_iff_mem_zmultiples"
namespace IndepSymm
p2m_open "ModularCurve"

theorem mem_zmultiples_symm {G : Type*} [AddCommGroup G] {p : ℕ} [hp : Fact p.Prime] {P Q : G}
    (hP0 : P ≠ 0) (hQ : p • Q = 0) (h : P ∈ AddSubgroup.zmultiples Q) :
    Q ∈ AddSubgroup.zmultiples P := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp h

  have hk : ((k : ℤ) : ZMod p) ≠ 0 := by
    intro hk0
    obtain ⟨t, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp hk0
    apply hP0
    rw [mul_comm, mul_zsmul, natCast_zsmul, hQ, zsmul_zero]
  set k' : ℤ := (((k : ZMod p)⁻¹ : ZMod p).val : ℤ) with hk'
  have hkk' : ((k * k' : ℤ) : ZMod p) = 1 := by
    rw [Int.cast_mul, hk', Int.cast_natCast, ZMod.natCast_zmod_val, mul_inv_cancel₀ hk]
  have hdvd : (p : ℤ) ∣ k * k' - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, hkk', Int.cast_one, sub_self]
  obtain ⟨t, ht⟩ := hdvd
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k', ?_⟩
  rw [smul_smul, mul_comm, show k * k' = 1 + t * p by linear_combination ht, add_zsmul, one_zsmul, mul_zsmul,
    natCast_zsmul, hQ, zsmul_zero, add_zero]

variable {A : Type u} [CommRing A]

theorem main (W : WeierstrassCurve A) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : IsUnit (p : A)) (hΔ : IsUnit W.Δ) {xP yP xQ yQ : A}
    (hPe : W.toAffine.Equation xP yP) (hQe : W.toAffine.Equation xQ yQ)
    (hψP : (W.preΨ (p : ℤ)).eval xP = 0) (hψQ : (W.preΨ (p : ℤ)).eval xQ = 0)
    (h : IsUnit (indepElt W p xP xQ)) :
    IsUnit (indepElt W p xQ xP) := by
  classical
  by_contra hnu
  obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits hnu

  let κ := A ⧸ M
  letI : Field κ := Ideal.Quotient.field M
  let π : A →+* κ := Ideal.Quotient.mk M
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2

  let W' : WeierstrassCurve κ := W.map π
  haveI hE : W'.IsElliptic := ⟨by rw [WeierstrassCurve.map_Δ]; exact hΔ.map π⟩

  have hPe' : W'.toAffine.Equation (π xP) (π yP) := hPe.map π
  have hQe' : W'.toAffine.Equation (π xQ) (π yQ) := hQe.map π
  have hPn : W'.toAffine.Nonsingular (π xP) (π yP) :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hPe'
  have hQn : W'.toAffine.Nonsingular (π xQ) (π yQ) :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hQe'

  have evmap : ∀ x : A, (W'.preΨ' p).eval (π x) = π ((W.preΨ (p : ℤ)).eval x) := by
    intro x
    rw [← WeierstrassCurve.preΨ_ofNat, WeierstrassCurve.map_preΨ, Polynomial.eval_map,
      Polynomial.eval₂_at_apply]
  have hPt : p • (WeierstrassCurve.Affine.Point.some (π xP) (π yP) hPn) = 0 := by
    rw [← natCast_zsmul]
    exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W'.toAffine hpodd hPn).mpr
      (by rw [evmap, hψP, map_zero])
  have hQt : p • (WeierstrassCurve.Affine.Point.some (π xQ) (π yQ) hQn) = 0 := by
    rw [← natCast_zsmul]
    exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W'.toAffine hpodd hQn).mpr
      (by rw [evmap, hψQ, map_zero])

  have h1 : indepElt W' p (π xP) (π xQ) ≠ 0 := by
    rw [indepElt_map]
    exact ((h.map π).ne_zero)
  have h2 : indepElt W' p (π xQ) (π xP) = 0 := by
    rw [indepElt_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hQnot : WeierstrassCurve.Affine.Point.some (π xQ) (π yQ) hQn ∉
      AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.some (π xP) (π yP) hPn) := fun hin =>
    h1 ((ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hp2 hPn hQn hPt).mpr hin)
  have hPin : WeierstrassCurve.Affine.Point.some (π xP) (π yP) hPn ∈
      AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.some (π xQ) (π yQ) hQn) :=
    (ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hp2 hQn hPn hQt).mp h2
  exact hQnot (mem_zmultiples_symm (WeierstrassCurve.Affine.Point.some_ne_zero hPn) hQt hPin)

end ModularCurve.IndepSymm

theorem solution
    {A : Type u} [CommRing A] (W : WeierstrassCurve A) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : IsUnit (p : A)) (hΔ : IsUnit W.Δ) {xP yP xQ yQ : A}
    (hP : W.toAffine.Equation xP yP) (hQ : W.toAffine.Equation xQ yQ)
    (hψP : (W.preΨ (p : ℤ)).eval xP = 0) (hψQ : (W.preΨ (p : ℤ)).eval xQ = 0)
    (h : IsUnit (ModularCurve.indepElt W p xP xQ)) :
    IsUnit (ModularCurve.indepElt W p xQ xP) :=
  ModularCurve.IndepSymm.main W p hp2 hp hΔ hP hQ hψP hψQ h

end S_ModularCurve_isUnit_indepElt_symm
end P2MW
export P2MW.S_ModularCurve_isUnit_indepElt_symm (solution)

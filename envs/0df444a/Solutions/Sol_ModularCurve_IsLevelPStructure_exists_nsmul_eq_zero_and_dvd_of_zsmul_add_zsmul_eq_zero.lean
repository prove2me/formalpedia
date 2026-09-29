-- Prove2me | solution 1 for ModularCurve.IsLevelPStructure.exists_nsmul_eq_zero_and_dvd_of_zsmul_add_zsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/47d1d25d-39f8-53d5-8689-03d0346ec2dc

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsLevelPStructure_exists_nsmul_eq_zero_and_dvd_of_zsmul_add_zsmul_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

universe u

namespace P2M
namespace ReadKatz

theorem exists_zsmul_zsmul_eq_of_not_dvd {V : Type*} [AddCommGroup V] {ℓ : ℕ} (hℓ : ℓ.Prime) {b : ℤ}
    (hb : ¬ (ℓ : ℤ) ∣ b) (Q : V) (hQ : ℓ • Q = 0) : ∃ v : ℤ, Q = v • (b • Q) := by
  have hcop : IsCoprime (ℓ : ℤ) b :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ).irreducible).mpr hb
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨v, ?_⟩
  have hℓQ : (ℓ : ℤ) • Q = 0 := by rw [natCast_zsmul]; exact hQ
  calc Q = (u * (ℓ : ℤ) + v * b) • Q := by rw [huv, one_zsmul]
    _ = u • ((ℓ : ℤ) • Q) + v • (b • Q) := by rw [add_smul, ← smul_smul, ← smul_smul]
    _ = v • (b • Q) := by rw [hℓQ, smul_zero, zero_add]

end P2M.ReadKatz

open P2M.ReadKatz in
theorem solution
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (D : ModularCurve.LevelPData F)
    (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    ∃ (hP : W.toAffine.Nonsingular D.xP D.yP) (hQ : W.toAffine.Nonsingular D.xQ D.yQ),
      ℓ • WeierstrassCurve.Affine.Point.some D.xP D.yP hP = 0 ∧
      ℓ • WeierstrassCurve.Affine.Point.some D.xQ D.yQ hQ = 0 ∧
      ∀ a b : ℤ, a • WeierstrassCurve.Affine.Point.some D.xP D.yP hP +
          b • WeierstrassCurve.Affine.Point.some D.xQ D.yQ hQ = 0 → (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b := by
  have hprime : ℓ.Prime := Fact.out
  have hodd : Odd ℓ := hprime.odd_of_ne_two hℓ2

  have hP : W.toAffine.Nonsingular D.xP D.yP := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hD.equation_P
  have hQ : W.toAffine.Nonsingular D.xQ D.yQ := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hD.equation_Q
  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some D.xP D.yP hP with hPdef
  set Q : W.toAffine.Point := WeierstrassCurve.Affine.Point.some D.xQ D.yQ hQ with hQdef

  have hℓP : ℓ • P = 0 := by
    rw [hPdef, WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd hP,
      ← WeierstrassCurve.preΨ_ofNat]
    exact hD.preΨ_P
  have hℓQ : ℓ • Q = 0 := by
    rw [hQdef, WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd hQ,
      ← WeierstrassCurve.preΨ_ofNat]
    exact hD.preΨ_Q

  have hQP : Q ∉ AddSubgroup.zmultiples P := by
    intro hmem
    have h0 : ModularCurve.indepElt W ℓ D.xP D.xQ = 0 :=
      (ModularCurve.indepElt_eq_zero_iff_mem_zmultiples (W := W) (p := ℓ) hℓ2 hP hQ hℓP).mpr hmem
    exact hD.isUnit_indepElt_PQ.ne_zero h0
  have hPQ : P ∉ AddSubgroup.zmultiples Q := by
    intro hmem
    have h0 : ModularCurve.indepElt W ℓ D.xQ D.xP = 0 :=
      (ModularCurve.indepElt_eq_zero_iff_mem_zmultiples (W := W) (p := ℓ) hℓ2 hQ hP hℓQ).mpr hmem
    exact hD.isUnit_indepElt_QP.ne_zero h0
  refine ⟨hP, hQ, hℓP, hℓQ, fun a b hab => ?_⟩

  have hb : (ℓ : ℤ) ∣ b := by
    by_contra hb
    obtain ⟨v, hv⟩ := exists_zsmul_zsmul_eq_of_not_dvd hprime hb Q hℓQ
    have hbQ : b • Q = -(a • P) := eq_neg_of_add_eq_zero_right hab
    apply hQP
    rw [hv, hbQ, smul_neg, smul_smul, ← neg_smul]
    exact AddSubgroup.zsmul_mem_zmultiples P _

  have ha : (ℓ : ℤ) ∣ a := by
    by_contra ha
    obtain ⟨v, hv⟩ := exists_zsmul_zsmul_eq_of_not_dvd hprime ha P hℓP
    have haP : a • P = -(b • Q) := eq_neg_of_add_eq_zero_left hab
    apply hPQ
    rw [hv, haP, smul_neg, smul_smul, ← neg_smul]
    exact AddSubgroup.zsmul_mem_zmultiples Q _
  exact ⟨ha, hb⟩

end S_ModularCurve_IsLevelPStructure_exists_nsmul_eq_zero_and_dvd_of_zsmul_add_zsmul_eq_zero
end P2MW
export P2MW.S_ModularCurve_IsLevelPStructure_exists_nsmul_eq_zero_and_dvd_of_zsmul_add_zsmul_eq_zero (solution)

-- Prove2me | solution 1 for ModularCurve.isGamma0PowAt_tateBase_prod_X_sub_C_toricPoint_fst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b176bff2-e39b-5be3-a889-4b676b9c41ee

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_isCyclicGenKernel_prod_X_sub_C_coordsOrZero_nsmul_of_addOrderOf_eq_pow
import Theorems.Thm_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two
import Theorems.Thm_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
import Theorems.Thm_ModularCurve_toricPoint_level_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isGamma0PowAt_tateBase_prod_X_sub_C_toricPoint_fst
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

noncomputable section

open Polynomial WeierstrassCurve ModularCurve

namespace P2MTateGenKernel

variable (F : Type u) [Field F]

abbrev W₁ : WeierstrassCurve (LaurentSeries F) := (tateLaurent F).baseChange (LaurentSeries F)

scoped instance : (W₁ F).IsElliptic := by
  unfold W₁ WeierstrassCurve.baseChange
  infer_instance

theorem W₁_map_qExpand (n : ℕ) [NeZero n] : (W₁ F).map (qExpand F n) = tateBase F n := by
  rw [W₁, WeierstrassCurve.baseChange, WeierstrassCurve.map_map, Algebra.algebraMap_self, RingHom.comp_id]
  rfl

variable {F}
variable {N : ℕ} (ζ : F) (hζ : IsPrimitiveRoot ζ N)
variable [DecidableEq (LaurentSeries F)]

include hζ in

theorem exists_point (hN : 1 ≤ N) :
    ∃ P : (W₁ F).toAffine.Point, addOrderOf P = N ∧
      ∀ a : ℕ, ¬ N ∣ a → (a • P).coordsOrZero.1 = (toricPoint F 1 (ζ ^ a)).1 := by
  rcases Nat.lt_or_ge N 2 with hN1 | hN2
  ·
    have hN1' : N = 1 := by omega
    subst hN1'
    refine ⟨0, addOrderOf_zero, fun a ha => absurd (one_dvd a) ha⟩
  obtain ⟨P, hP, hP'⟩ := ModularCurve.exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot F N
    hN2 ζ hζ (LaurentSeries F)
  refine ⟨P, ?_, ?_⟩
  · rw [addOrderOf_eq_iff (by omega)]
    refine ⟨(hP N).mpr dvd_rfl, fun m hm hm0 h => ?_⟩
    have := (hP m).mp h
    exact absurd (Nat.le_of_dvd hm0 this) (not_le.mpr hm)
  · intro a ha
    obtain ⟨hns, ha'⟩ := hP' a ha
    rw [ha', Affine.Point.coordsOrZero_some]
    rfl

theorem toricPoint_fst_eq_qExpand (n : ℕ) [NeZero n] (c : F) :
    (toricPoint F n c).1 = qExpand F n (toricPoint F 1 c).1 := by
  have h := ModularCurve.toricPoint_level_mul F 1 n c
  rw [mul_one] at h
  rw [h]

end P2MTateGenKernel
p2m_reactivate "P2MW.S_ModularCurve_isGamma0PowAt_tateBase_prod_X_sub_C_toricPoint_fst.P2MTateGenKernel"

end
p2m_reactivate "P2MW.S_ModularCurve_isGamma0PowAt_tateBase_prod_X_sub_C_toricPoint_fst.P2MTateGenKernel"

open Polynomial in
theorem solution
    (F : Type u) [Field F] (p k : ℕ) [Fact p.Prime] (ζ : F) (hζ : IsPrimitiveRoot ζ (p ^ k))
    (n : ℕ) [NeZero n] :
    ModularCurve.IsGamma0PowAt (ModularCurve.tateBase F n) p k
      (∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
        (X - C (ModularCurve.toricPoint F n (ζ ^ a)).1)) := by
  classical
  have hp : p.Prime := Fact.out
  have hNpos : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  obtain ⟨P, hPN, hPa⟩ := P2MTateGenKernel.exists_point ζ hζ hNpos

  have hidx : ∀ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), ¬ p ^ k ∣ a := by
    intro a ha h
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    have := Nat.le_of_dvd (by omega) h
    have : p ^ k / 2 < p ^ k := Nat.div_lt_self (by omega) one_lt_two
    omega
  have hW₁ : ModularCurve.IsGamma0PowAt (P2MTateGenKernel.W₁ F) p k
      (∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), (X - C (ModularCurve.toricPoint F 1 (ζ ^ a)).1)) := by
    have hprod : (∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), (X - C (ModularCurve.toricPoint F 1 (ζ ^ a)).1)) =
        ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), (X - C ((a • P).coordsOrZero).1) := by
      refine Finset.prod_congr rfl fun a ha => ?_
      rw [hPa a (hidx a ha)]
    rw [hprod]
    by_cases hpk : p ^ k = 2
    · rw [ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk]
      have hset : (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a) = {1} := by
        have hp2 : p = 2 := by
          have h2 : p ∣ 2 := by rw [← hpk]; exact dvd_pow_self p (by rintro rfl; simp at hpk)
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
        rw [hpk]
        ext a
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, hp2]
        omega
      rw [hset, Finset.prod_singleton, one_smul]
      rw [hpk] at hPN
      exact WeierstrassCurve.isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two _ P hPN
    · rw [ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk]
      exact WeierstrassCurve.isCyclicGenKernel_prod_X_sub_C_coordsOrZero_nsmul_of_addOrderOf_eq_pow _ p k hpk P hPN

  have hmap := ModularCurve.IsGamma0PowAt.map (ModularCurve.qExpand F n) (P2MTateGenKernel.W₁ F) p k hW₁
  rw [P2MTateGenKernel.W₁_map_qExpand, Polynomial.map_prod] at hmap
  convert hmap using 2 with a ha
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, P2MTateGenKernel.toricPoint_fst_eq_qExpand]

end S_ModularCurve_isGamma0PowAt_tateBase_prod_X_sub_C_toricPoint_fst
end P2MW
export P2MW.S_ModularCurve_isGamma0PowAt_tateBase_prod_X_sub_C_toricPoint_fst (solution)

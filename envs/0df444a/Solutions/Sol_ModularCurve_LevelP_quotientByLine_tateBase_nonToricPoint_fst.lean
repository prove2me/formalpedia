-- Prove2me | solution 1 for ModularCurve.LevelP.quotientByLine_tateBase_nonToricPoint_fst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/0f5f2e4e-ab48-51c8-9ceb-8e1fd190887c

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPQuotient
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_veluQuotient_nonToricSlotSet
import Theorems.Thm_ModularCurve_tateUniv_equation
import Theorems.Thm_ModularCurve_nonToricPoint_fst_mul_psiSq_eq_phi
import Theorems.Thm_WeierstrassCurve_eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero
import Theorems.Thm_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero
import Theorems.Thm_ModularCurve_equation_tateBase_nonToricPoint
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelP_quotientByLine_tateBase_nonToricPoint_fst
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃"

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

namespace ModularCurve
p2m_export "ModularCurve" "LevelP.quotientByLine LevelP.quotientByLine_a₄ LevelP.quotientByLine_a₆ tateLaurent tateUnivX slotSubst nonToricPoint nonToricSlotSet tateBase nonToricPoint_fst qTwist qTwist_one_apply veluQuotient_nonToricSlotSet tateUniv_equation nonToricPoint_fst_mul_psiSq_eq_phi eval_prePsi_tateBase_nonToricPoint_eq_zero equation_tateBase_nonToricPoint coeff_slotSubst_tateUnivX"
namespace LevelP
p2m_export "ModularCurve.LevelP" "smulX smulX_mul_ΨSq veluTLine veluWLine quotientByLine quotientByLine_a₄ quotientByLine_a₆"
namespace Cusp
p2m_open "ModularCurve.LevelP ModularCurve"

p2m_open "WeierstrassCurve Polynomial ModularCurve P2MW.S_ModularCurve_LevelP_quotientByLine_tateBase_nonToricPoint_fst.ModularCurve ModularCurve.LevelP P2MW.S_ModularCurve_LevelP_quotientByLine_tateBase_nonToricPoint_fst.ModularCurve.LevelP"

section LowCoeff

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime]

theorem slotSubstX_coeff_low (hp3 : 3 ≤ p) (c : Kˣ) (j : ℕ) (h1j : 1 ≤ j) (hjp : j ≤ p / 2) :
    (∀ n < j, PowerSeries.coeff n (slotSubst K p c j tateUnivX) = 0) ∧
    PowerSeries.coeff j (slotSubst K p c j tateUnivX) = (c : K) := by
  have hjp' : j < p := lt_of_le_of_lt hjp
    (Nat.div_lt_self ((Fact.out : p.Prime).pos) one_lt_two)
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h2j : 2 * j < p := by rcases hodd with ⟨w, hw⟩; omega
  have tails (n : ℕ) (hn : n ≤ j) :
      (∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
        (e : K) * (((if n = p * M + j * e then (c : K) ^ e else 0)
          + if n + j * e = p * M then (↑c⁻¹ : K) ^ e else 0)
          - if n = p * M then 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun M hM => Finset.sum_eq_zero fun e he => ?_
    rcases Nat.eq_zero_or_pos M with rfl | hM1
    · simp at he
    have heM : e ≤ M := Nat.le_of_dvd hM1 (Nat.mem_divisors.mp he).1
    have hMn : M ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hM)
    have h1 : ¬ n = p * M + j * e := by nlinarith [hM1, hjp']
    have h3 : ¬ n = p * M := by nlinarith [hM1, hjp']
    have h2 : ¬ n + j * e = p * M := by
      intro heq
      have : n ≥ (p - j) * M := by nlinarith [heM]
      have : p - j ≤ n := le_trans (Nat.le_mul_of_pos_right _ hM1) this
      omega
    simp [h1, h2, h3]
  constructor
  · intro n hn
    rw [coeff_slotSubst_tateUnivX p c j h1j hjp' n, tails n hn.le, add_zero]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · exact if_neg fun hd => absurd (Nat.le_of_dvd hn0 hd) (not_le.mpr hn)
  · rw [coeff_slotSubst_tateUnivX p c j h1j hjp' j, tails j le_rfl, add_zero,
      if_pos (dvd_refl j), Nat.div_self h1j, Nat.cast_one, one_mul, pow_one]

theorem nonToricPoint_one_injOn [Nontrivial K] (hp3 : 3 ≤ p) :
    Set.InjOn (fun k : ℕ => nonToricPoint K p ((1 : Kˣ) ^ (0 * k)) k) (Finset.Icc 1 (p / 2) : Set ℕ) := by
  intro k₁ hk₁ k₂ hk₂ h
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk₁ hk₂
  simp only [one_pow] at h
  by_contra hne
  have hX : slotSubst K p 1 k₁ tateUnivX = slotSubst K p 1 k₂ tateUnivX := by
    have h1 := congrArg Prod.fst h
    rw [nonToricPoint_fst, nonToricPoint_fst] at h1
    exact HahnSeries.ofPowerSeries_injective h1
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have a := (slotSubstX_coeff_low K p hp3 1 k₁ hk₁.1 hk₁.2).2
    have b := (slotSubstX_coeff_low K p hp3 1 k₂ hk₂.1 hk₂.2).1 k₁ hlt
    rw [hX, b, Units.val_one] at a
    exact zero_ne_one a
  · have a := (slotSubstX_coeff_low K p hp3 1 k₂ hk₂.1 hk₂.2).2
    have b := (slotSubstX_coeff_low K p hp3 1 k₁ hk₁.1 hk₁.2).1 k₂ hlt
    rw [← hX, b, Units.val_one] at a
    exact zero_ne_one a

end LowCoeff

section Main

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]

theorem isUnit_p_mul_Δ (hp : IsUnit (p : R)) :
    IsUnit ((p : LaurentSeries R) * (tateBase R p).Δ) := by
  refine IsUnit.mul ?_ (tateBase R p).isUnit_Δ
  simpa using hp.map (algebraMap R (LaurentSeries R))

theorem isUnit_ΨSq_x1 (hp2 : p ≠ 2) (hp : IsUnit (p : R)) (a : ℕ)
    (ha : a ∈ Finset.Icc 1 ((p - 1) / 2)) :
    IsUnit (((tateBase R p).ΨSq a).eval (nonToricPoint R p 1 1).1) := by
  have hpr : p.Prime := Fact.out
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  have hlt : a < p := by have := Nat.div_le_self (p - 1) 2; omega
  have hnd : ¬ (p : ℤ) ∣ (a : ℤ) := by
    intro hdvd
    have := Nat.le_of_dvd (by omega) (Int.natCast_dvd_natCast.mp hdvd)
    omega
  have hx := ModularCurve.eval_prePsi_tateBase_nonToricPoint_eq_zero R p hp2 1 (one_pow p) 1 one_pos
    hpr.one_lt
  exact (WeierstrassCurve.eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero (tateBase R p) hp2
    (isUnit_p_mul_Δ R p hp) hx hnd).1

theorem smulX_x1 (hp2 : p ≠ 2) (hp : IsUnit (p : R)) (a : ℕ)
    (ha : a ∈ Finset.Icc 1 ((p - 1) / 2)) :
    smulX (tateBase R p) a (nonToricPoint R p 1 1).1 = (nonToricPoint R p 1 a).1 := by
  have hpr : p.Prime := Fact.out
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  have hlt : a < p := by have := Nat.div_le_self (p - 1) 2; omega
  have hap : a ≤ p / 2 := by have := Nat.div_le_div_right (c := 2) (Nat.sub_le p 1); omega
  have hU := isUnit_ΨSq_x1 R p hp2 hp a ha
  have H := ModularCurve.nonToricPoint_fst_mul_psiSq_eq_phi R p 1 (one_pow p) 0 1 a one_pos hpr.one_lt
    ha1 hap
  simp only [one_pow, mul_one, Nat.mod_eq_of_lt hlt] at H
  rw [← hU.mul_left_inj, smulX_mul_ΨSq (tateBase R p) hU, H]

theorem veluTLine_eq [Nontrivial R] (hp2 : p ≠ 2) (hp : IsUnit (p : R)) :
    veluTLine (tateBase R p) p (nonToricPoint R p 1 1).1 =
      (tateBase R p).veluTSum (nonToricSlotSet R p 1 0) := by
  classical
  have hpr : p.Prime := Fact.out
  have hodd : Odd p := hpr.odd_of_ne_two hp2
  have hhalf : (p - 1) / 2 = p / 2 := by obtain ⟨m, hm⟩ := hodd; omega
  have hp3 : 3 ≤ p := by have := hpr.two_le; omega
  rw [WeierstrassCurve.veluTSum, nonToricSlotSet, Finset.sum_image (nonToricPoint_one_injOn R p hp3),
    veluTLine, hhalf]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [smulX_x1 R p hp2 hp a (hhalf ▸ ha), one_pow, WeierstrassCurve.veluT_eq]

theorem veluWLine_eq [Nontrivial R] (hp2 : p ≠ 2) (hp : IsUnit (p : R)) :
    veluWLine (tateBase R p) p (nonToricPoint R p 1 1).1 =
      (tateBase R p).veluWSum (nonToricSlotSet R p 1 0) := by
  classical
  have hpr : p.Prime := Fact.out
  have hodd : Odd p := hpr.odd_of_ne_two hp2
  have hhalf : (p - 1) / 2 = p / 2 := by obtain ⟨m, hm⟩ := hodd; omega
  have hp3 : 3 ≤ p := by have := hpr.two_le; omega
  rw [WeierstrassCurve.veluWSum, nonToricSlotSet, Finset.sum_image (nonToricPoint_one_injOn R p hp3),
    veluWLine, hhalf]
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  have hlt : a < p := by omega
  rw [smulX_x1 R p hp2 hp a (hhalf ▸ ha), one_pow, WeierstrassCurve.veluW, WeierstrassCurve.veluT_eq,
    WeierstrassCurve.veluU_eq_Ψ₂Sq_eval _
      (ModularCurve.equation_tateBase_nonToricPoint R p 1 a (by omega) hlt)]

end Main

end ModularCurve.LevelP.Cusp

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_LevelP_quotientByLine_tateBase_nonToricPoint_fst.ModularCurve _root_.ModularCurve.LevelP _root_.P2MW.S_ModularCurve_LevelP_quotientByLine_tateBase_nonToricPoint_fst.ModularCurve.LevelP WeierstrassCurve in

theorem solution
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R)) :
    ModularCurve.LevelP.quotientByLine (ModularCurve.tateBase R p) p
        (ModularCurve.nonToricPoint R p 1 1).1 = ModularCurve.tateLaurent R := by
  classical
  have hpr : p.Prime := Fact.out
  rcases subsingleton_or_nontrivial R with hR | hR
  · have hS : ∀ a b : LaurentSeries R, a = b := fun a b => by
      ext n; exact Subsingleton.elim _ _
    exact WeierstrassCurve.ext (hS _ _) (hS _ _) (hS _ _) (hS _ _) (hS _ _)
  have hodd : Odd p := hpr.odd_of_ne_two hp2
  have hV := ModularCurve.veluQuotient_nonToricSlotSet R p hodd 1 (one_pow p) 0
    ModularCurve.tateUniv_equation
  have hid : (tateLaurent R).map (qTwist ((1 : Rˣ) ^ 0)) = tateLaurent R := by
    rw [pow_zero]
    ext <;> simp [WeierstrassCurve.map, ModularCurve.qTwist_one_apply]
  rw [hid] at hV
  rw [← hV]
  have hT := ModularCurve.LevelP.Cusp.veluTLine_eq R p hp2 hp
  have hW := ModularCurve.LevelP.Cusp.veluWLine_eq R p hp2 hp
  ext
  · rfl
  · rfl
  · rfl
  · rw [LevelP.quotientByLine_a₄, WeierstrassCurve.veluQuotient_a₄, hT]
  · rw [LevelP.quotientByLine_a₆, WeierstrassCurve.veluQuotient_a₆, hT, hW]

end S_ModularCurve_LevelP_quotientByLine_tateBase_nonToricPoint_fst
end P2MW
export P2MW.S_ModularCurve_LevelP_quotientByLine_tateBase_nonToricPoint_fst (solution)

-- Prove2me | solution 1 for ModularCurve.eval_prePsi_tateBase_nonToricPoint_eq_zero_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/2abfdb76-e2d0-5b8b-ba11-44444bbe5e52

import Mathlib
import Definitions.Def_LaurentSeries_XAdic
import Definitions.Def_TateCurve_PointSeries
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_TateCurve_isRoot_prePsi_curve_pointX_laurentSeries
import Theorems.Thm_ModularCurve_tateCurve_curve_X_pow_eq_tateBase
import Theorems.Thm_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero_of_five_le
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero_of_five_le.ModularCurve HahnSeries Polynomial"
open scoped LaurentSeries.XAdic

universe u

namespace ModularCurve
p2m_export "ModularCurve" "tateUnivX slotSubst nonToricPoint tateBase nonToricPoint_fst laurentOfInt laurentOfInt_apply tateLaurent qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd coeffMap coeffMap_coeff tateCurve_curve_X_pow_eq_tateBase tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst coeff_slotSubst_tateUnivX"
namespace SlotTorsion
p2m_open "ModularCurve"

section Naturality

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)

theorem coeffMap_ofPowerSeries (g : PowerSeries A) :
    coeffMap f (ofPowerSeries ℤ A g) = ofPowerSeries ℤ B (PowerSeries.map f g) := by
  ext n
  rw [coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · exact map_zero f
  · rw [PowerSeries.coeff_map]

theorem coeffMap_laurentOfInt (g : PowerSeries ℤ) :
    coeffMap f (laurentOfInt A g) = laurentOfInt B g := by
  rw [laurentOfInt_apply, laurentOfInt_apply, coeffMap_ofPowerSeries]
  congr 1
  ext n
  simp only [PowerSeries.coeff_map, eq_intCast, map_intCast]

theorem coeffMap_qExpand (N : ℕ) [NeZero N] (x : LaurentSeries A) :
    coeffMap f (qExpand A N x) = qExpand B N (coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem tateBase_map_coeffMap (p : ℕ) [NeZero p] :
    (tateBase A p).map (coeffMap f) = tateBase B p := by
  simp only [tateBase, tateLaurent, WeierstrassCurve.map, coeffMap_qExpand, coeffMap_laurentOfInt]

theorem map_slotSubst_tateUnivX (p : ℕ) (c : Aˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    PowerSeries.map f (slotSubst A p c j tateUnivX) = slotSubst B p (Units.map (f : A →* B) c) j tateUnivX := by
  ext n
  rw [PowerSeries.coeff_map, coeff_slotSubst_tateUnivX p c j hj hjp n,
    coeff_slotSubst_tateUnivX p (Units.map (f : A →* B) c) j hj hjp n]
  simp only [map_add, map_sub, map_sum, map_mul, map_pow, map_natCast, map_ofNat, map_zero,
    apply_ite f, Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

theorem coeffMap_nonToricPoint_fst (p : ℕ) (c : Aˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    coeffMap f (nonToricPoint A p c j).1 = (nonToricPoint B p (Units.map (f : A →* B) c) j).1 := by
  rw [nonToricPoint_fst, nonToricPoint_fst, coeffMap_ofPowerSeries, map_slotSubst_tateUnivX f p c j hj hjp]

theorem coeffMap_eval_preΨ (p : ℕ) [NeZero p] (n : ℤ) (c : Aˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    coeffMap f (((tateBase A p).preΨ n).eval (nonToricPoint A p c j).1)
      = ((tateBase B p).preΨ n).eval (nonToricPoint B p (Units.map (f : A →* B) c) j).1 := by
  rw [← coeffMap_nonToricPoint_fst f p c j hj hjp, ← tateBase_map_coeffMap f p, WeierstrassCurve.map_preΨ,
    Polynomial.eval_map, Polynomial.eval₂_at_apply]

end Naturality

section Universal

variable (p : ℕ) [hp : Fact p.Prime]

abbrev Auniv : Type := AdjoinRoot (X ^ p - 1 : ℤ[X])

def ρ : Auniv p := AdjoinRoot.root (X ^ p - 1)

theorem ρ_pow : ρ p ^ p = 1 := by
  have h := AdjoinRoot.eval₂_root (X ^ p - 1 : ℤ[X])
  rw [eval₂_sub, eval₂_X_pow, eval₂_one, sub_eq_zero] at h
  exact h

def cA : (Auniv p)ˣ :=
  Units.mkOfMulEqOne (ρ p) (ρ p ^ (p - 1)) (by rw [← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le, ρ_pow])

@[scoped simp] theorem val_cA : (cA p : Auniv p) = ρ p := rfl

theorem cA_pow : cA p ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, val_cA, ρ_pow, Units.val_one])

def toRing (K : Type*) [CommRing K] (c : K) (hc : c ^ p = 1) : Auniv p →+* K :=
  AdjoinRoot.lift (Int.castRingHom K) c (by rw [eval₂_sub, eval₂_X_pow, eval₂_one, hc, sub_self])

theorem toRing_ρ (K : Type*) [CommRing K] (c : K) (hc : c ^ p = 1) : toRing p K c hc (ρ p) = c :=
  AdjoinRoot.lift_root _

theorem toRing_cA (K : Type*) [CommRing K] (c : Kˣ) (hc : c ^ p = 1) :
    Units.map (toRing p K c (by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]) : Auniv p →* K) (cA p) = c :=
  Units.ext (by rw [Units.coe_map, MonoidHom.coe_coe, val_cA, toRing_ρ])

def ζℂ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

theorem ζℂ_spec : IsPrimitiveRoot (ζℂ p) p := Complex.isPrimitiveRoot_exp p hp.out.ne_zero

def ζℂu : ℂˣ := Units.mk0 (ζℂ p) ((ζℂ_spec p).ne_zero hp.out.ne_zero)

@[scoped simp] theorem val_ζℂu : (ζℂu p : ℂ) = ζℂ p := rfl

def g₁ : Auniv p →+* ℂ := toRing p ℂ 1 (one_pow p)

def g₂ : Auniv p →+* ℂ := toRing p ℂ (ζℂ p) (ζℂ_spec p).pow_eq_one

theorem g₁_cA : Units.map (g₁ p : Auniv p →* ℂ) (cA p) = (ζℂu p) ^ 0 := by
  rw [pow_zero]; exact Units.ext (by rw [Units.coe_map, MonoidHom.coe_coe, val_cA, g₁, toRing_ρ, Units.val_one])

theorem g₂_cA : Units.map (g₂ p : Auniv p →* ℂ) (cA p) = (ζℂu p) ^ 1 := by
  rw [pow_one]; exact Units.ext (by rw [Units.coe_map, MonoidHom.coe_coe, val_cA, g₂, toRing_ρ, val_ζℂu])

set_option maxHeartbeats 3200000 in

theorem eq_zero_of_g₁_g₂ (hp2 : p ≠ 2) (a : Auniv p) (h₁ : g₁ p a = 0) (h₂ : g₂ p a = 0) : a = 0 := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [g₁, toRing, AdjoinRoot.lift_mk, eval₂_at_one, eq_intCast, Int.cast_eq_zero] at h₁
  rw [g₂, toRing, AdjoinRoot.lift_mk] at h₂

  have hd1 : (X - Polynomial.C (1 : ℤ)) ∣ q := dvd_iff_isRoot.mpr h₁
  have hd2 : cyclotomic p ℤ ∣ q := by
    rw [cyclotomic_eq_minpoly (ζℂ_spec p) hp.out.pos]
    refine minpoly.isIntegrallyClosed_dvd ((ζℂ_spec p).isIntegral hp.out.pos) ?_
    rwa [Polynomial.aeval_def, algebraMap_int_eq]

  have hprime : Prime (cyclotomic p ℤ) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (cyclotomic.irreducible hp.out.pos)
  have hndvd : ¬ cyclotomic p ℤ ∣ (X - Polynomial.C (1 : ℤ)) := by
    intro h
    have h1 := natDegree_le_of_dvd h (X_sub_C_ne_zero 1)
    rw [natDegree_cyclotomic, Nat.totient_prime hp.out, natDegree_X_sub_C] at h1
    have := hp.out.two_le
    omega
  obtain ⟨r, hr⟩ := hd1
  have hdr : cyclotomic p ℤ ∣ r := by
    rcases hprime.dvd_or_dvd (hr ▸ hd2) with h | h
    · exact absurd h hndvd
    · exact h
  obtain ⟨s, rfl⟩ := hdr
  refine AdjoinRoot.mk_eq_zero.mpr ⟨s, ?_⟩
  rw [hr, ← cyclotomic_prime_mul_X_sub_one ℤ p, map_one]
  ring

end Universal

section Main

variable (p : ℕ) [hp : Fact p.Prime]

theorem field_case (hp5 : 5 ≤ p) (i : ℕ) (hi : i < p) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    ((tateBase ℂ p).preΨ (p : ℤ)).eval (nonToricPoint ℂ p ((ζℂu p) ^ i) j).1 = 0 := by
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have h := TateCurve.isRoot_prePsi_curve_pointX_laurentSeries ℂ p hodd hp5 (ζℂ p) (ζℂ_spec p) i j hi hjp
    (fun h => hj.ne' h.2)
  have hCpow : ((HahnSeries.C : ℂ →+* LaurentSeries ℂ) (ζℂ p)) ^ i = HahnSeries.C ((((ζℂu p) ^ i : ℂˣ) : ℂ)) := by
    rw [Units.val_pow_eq_pow_val, val_ζℂu, map_pow]
  rw [ModularCurve.tateCurve_curve_X_pow_eq_tateBase ℂ p, hCpow,
    ModularCurve.tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst ℂ p ((ζℂu p) ^ i) j hj hjp,
    ← WeierstrassCurve.preΨ_ofNat] at h
  exact h.eq_zero

theorem main (K : Type u) [CommRing K] (hp5 : 5 ≤ p) (c : Kˣ) (hc : c ^ p = 1) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    ((tateBase K p).preΨ (p : ℤ)).eval (nonToricPoint K p c j).1 = 0 := by
  have hc' : (c : K) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]

  have hA : ((tateBase (Auniv p) p).preΨ (p : ℤ)).eval (nonToricPoint (Auniv p) p (cA p) j).1 = 0 := by
    ext n
    rw [HahnSeries.coeff_zero]
    apply eq_zero_of_g₁_g₂ p (by omega)
    · rw [← coeffMap_coeff, coeffMap_eval_preΨ (g₁ p) p (p : ℤ) (cA p) j hj hjp, g₁_cA,
        field_case p hp5 0 hp.out.pos j hj hjp, HahnSeries.coeff_zero]
    · rw [← coeffMap_coeff, coeffMap_eval_preΨ (g₂ p) p (p : ℤ) (cA p) j hj hjp, g₂_cA,
        field_case p hp5 1 hp.out.one_lt j hj hjp, HahnSeries.coeff_zero]
  have h := congrArg (coeffMap (toRing p K c hc')) hA
  rwa [map_zero, coeffMap_eval_preΨ _ p _ _ j hj hjp, toRing_cA p K c hc] at h

end Main

end ModularCurve.SlotTorsion
p2m_reactivate "P2MW.S_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero_of_five_le.ModularCurve P2MW.S_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero_of_five_le.ModularCurve.SlotTorsion"
p2m_reactivate "P2MW.S_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero_of_five_le.ModularCurve"

theorem solution
    (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (c : Kˣ) (hc : c ^ p = 1)
    (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    ((ModularCurve.tateBase K p).preΨ (p : ℤ)).eval (ModularCurve.nonToricPoint K p c j).1 = 0 :=
  ModularCurve.SlotTorsion.main p K hp5 c hc j hj hjp

end
p2m_reactivate "P2MW.S_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero_of_five_le.ModularCurve P2MW.S_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero_of_five_le.ModularCurve.SlotTorsion"

end S_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero_of_five_le
end P2MW
export P2MW.S_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero_of_five_le (solution)

-- Prove2me | solution 1 for ModularCurve.eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c6c03459-aeba-5e39-b57b-ecb2697e5945

import Mathlib
import Definitions.Def_LaurentSeries_XAdic
import Definitions.Def_TateCurve_PointSeries
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_TateCurve_isRoot_prePsi_curve_pointX_laurentSeries
import Theorems.Thm_ModularCurve_tateCurve_curve_X_pow_eq_tateBase
import Theorems.Thm_ModularCurve_tateCurve_pointX_C_eq_tateToricPoint_fst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le.ModularCurve HahnSeries Polynomial"
open scoped LaurentSeries.XAdic

universe u

namespace ModularCurve
p2m_export "ModularCurve" "tateBase laurentOfInt laurentOfInt_apply tateLaurent qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd coeffMap coeffMap_coeff tateToricPoint tateToricPoint_fst tateCurve_curve_X_pow_eq_tateBase tateCurve_pointX_C_eq_tateToricPoint_fst"
namespace ToricTorsion
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

theorem map_ringInverse {x : A} (hx : IsUnit x) : f (Ring.inverse x) = Ring.inverse (f x) := by
  obtain ⟨u, rfl⟩ := hx
  rw [Ring.inverse_unit, show f (u : A) = ((Units.map (f : A →* B) u : Bˣ) : B) from rfl,
    Ring.inverse_unit, Units.coe_map_inv, MonoidHom.coe_coe]

theorem coeffMap_tateToricPoint_fst (p : ℕ) (c : Aˣ) (hc : IsUnit (1 - (c : A))) :
    coeffMap f (tateToricPoint A p c).1 = (tateToricPoint B p (Units.map (f : A →* B) c)).1 := by
  have h1 : f (Ring.inverse (1 - (c : A))) = Ring.inverse (1 - ((Units.map (f : A →* B) c : Bˣ) : B)) := by
    rw [map_ringInverse f hc, map_sub, map_one, Units.coe_map, MonoidHom.coe_coe]
  rw [tateToricPoint_fst, tateToricPoint_fst, coeffMap_ofPowerSeries]
  congr 1
  ext m
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm, map_mul, map_pow, h1, Units.coe_map, MonoidHom.coe_coe]
  · rw [if_neg hm, if_neg hm]
    simp only [map_add, map_sub, map_sum, map_mul, map_pow, map_natCast, map_zero, map_ofNat,
      apply_ite f, Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

theorem coeffMap_injective (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem coeffMap_eval_preΨ (p : ℕ) [NeZero p] (n : ℤ) (c : Aˣ) (hc : IsUnit (1 - (c : A))) :
    coeffMap f (((tateBase A p).preΨ n).eval (tateToricPoint A p c).1)
      = ((tateBase B p).preΨ n).eval (tateToricPoint B p (Units.map (f : A →* B) c)).1 := by
  rw [← coeffMap_tateToricPoint_fst f p c hc, ← tateBase_map_coeffMap f p, WeierstrassCurve.map_preΨ,
    Polynomial.eval_map, Polynomial.eval₂_at_apply]

end Naturality

section Universal

variable (p : ℕ) [hp : Fact p.Prime]

abbrev Acyc : Type := AdjoinRoot (cyclotomic p ℤ)

def ρ : Acyc p := AdjoinRoot.root (cyclotomic p ℤ)

theorem ρ_pow : ρ p ^ p = 1 := by
  have hdvd : cyclotomic p ℤ ∣ X ^ p - 1 := cyclotomic.dvd_X_pow_sub_one p ℤ
  have h0 : AdjoinRoot.mk (cyclotomic p ℤ) (X ^ p - 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hdvd
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h0
  exact h0

abbrev Bcyc : Type := Localization.Away (1 - ρ p)

def cB : (Bcyc p)ˣ :=
  Units.mkOfMulEqOne (algebraMap (Acyc p) (Bcyc p) (ρ p)) (algebraMap (Acyc p) (Bcyc p) (ρ p ^ (p - 1))) (by
    rw [← map_mul, ← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le, ρ_pow, map_one])

@[scoped simp] theorem val_cB : (cB p : Bcyc p) = algebraMap (Acyc p) (Bcyc p) (ρ p) := rfl

theorem cB_pow : cB p ^ p = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, val_cB, ← map_pow, ρ_pow, map_one, Units.val_one])

theorem isUnit_one_sub_cB : IsUnit (1 - (cB p : Bcyc p)) := by
  rw [val_cB, ← map_one (algebraMap (Acyc p) (Bcyc p)), ← map_sub]
  exact IsLocalization.Away.algebraMap_isUnit (1 - ρ p)

theorem eval₂_cyclotomic_int_eq_zero {K : Type*} [CommRing K] (c : K) (hc : c ^ p = 1) (h1c : IsUnit (1 - c)) :
    eval₂ (Int.castRingHom K) c (cyclotomic p ℤ) = 0 := by
  rw [eval₂_eq_eval_map, map_cyclotomic_int]
  have key : (cyclotomic p K).eval c * (c - 1) = 0 := by
    have := congrArg (Polynomial.eval c) (cyclotomic_prime_mul_X_sub_one K p)
    simpa [hc] using this
  have hu : IsUnit (c - 1) := by rw [← neg_sub]; exact h1c.neg
  exact (hu.mul_left_eq_zero).mp key

def toRing (K : Type*) [CommRing K] (c : K) (hc : c ^ p = 1) (h1c : IsUnit (1 - c)) : Bcyc p →+* K :=
  IsLocalization.Away.lift (1 - ρ p)
    (g := AdjoinRoot.lift (Int.castRingHom K) c (eval₂_cyclotomic_int_eq_zero p c hc h1c))
    (by rwa [map_sub, map_one, ρ, AdjoinRoot.lift_root])

theorem toRing_algebraMap (K : Type*) [CommRing K] (c : K) (hc : c ^ p = 1) (h1c : IsUnit (1 - c)) (a : Acyc p) :
    toRing p K c hc h1c (algebraMap (Acyc p) (Bcyc p) a)
      = AdjoinRoot.lift (Int.castRingHom K) c (eval₂_cyclotomic_int_eq_zero p c hc h1c) a :=
  IsLocalization.Away.lift_eq _ _ a

theorem toRing_cB (K : Type*) [CommRing K] (c : Kˣ) (hc : c ^ p = 1) (h1c : IsUnit (1 - (c : K))) :
    Units.map (toRing p K c (by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]) h1c : Bcyc p →* K) (cB p) = c :=
  Units.ext (by rw [Units.coe_map, MonoidHom.coe_coe, val_cB, toRing_algebraMap, ρ, AdjoinRoot.lift_root])

def ζℂ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

theorem ζℂ_spec : IsPrimitiveRoot (ζℂ p) p := Complex.isPrimitiveRoot_exp p hp.out.ne_zero

theorem ζℂ_ne_one : ζℂ p ≠ 1 := (ζℂ_spec p).ne_one hp.out.one_lt

def ζℂu : ℂˣ := Units.mk0 (ζℂ p) ((ζℂ_spec p).ne_zero hp.out.ne_zero)

@[scoped simp] theorem val_ζℂu : (ζℂu p : ℂ) = ζℂ p := rfl

theorem isUnit_one_sub_ζℂ : IsUnit (1 - ζℂ p) :=
  isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (ζℂ_ne_one p).symm)

def toC : Bcyc p →+* ℂ := toRing p ℂ (ζℂ p) (ζℂ_spec p).pow_eq_one (isUnit_one_sub_ζℂ p)

theorem toC_cB : Units.map (toC p : Bcyc p →* ℂ) (cB p) = ζℂu p := by
  refine Units.ext ?_
  rw [Units.coe_map, MonoidHom.coe_coe, val_cB, toC, toRing_algebraMap, ρ, AdjoinRoot.lift_root, val_ζℂu]

theorem lift_injective :
    Function.Injective (AdjoinRoot.lift (Int.castRingHom ℂ) (ζℂ p)
      (eval₂_cyclotomic_int_eq_zero p (ζℂ p) (ζℂ_spec p).pow_eq_one (isUnit_one_sub_ζℂ p))) := by
  refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [AdjoinRoot.lift_mk] at ha
  rw [AdjoinRoot.mk_eq_zero, cyclotomic_eq_minpoly (ζℂ_spec p) hp.out.pos]
  refine minpoly.isIntegrallyClosed_dvd ((ζℂ_spec p).isIntegral hp.out.pos) ?_
  rwa [Polynomial.aeval_def, algebraMap_int_eq]

theorem toC_injective : Function.Injective (toC p) := by
  refine (injective_iff_map_eq_zero _).mpr fun b hb => ?_
  obtain ⟨⟨a, s⟩, hbs⟩ := IsLocalization.surj (Submonoid.powers (1 - ρ p)) b
  have h := congrArg (toC p) hbs
  rw [map_mul, hb, zero_mul, toC, toRing_algebraMap] at h
  have ha : a = 0 := (injective_iff_map_eq_zero _).mp (lift_injective p) a h.symm
  rw [ha, map_zero] at hbs
  exact (IsLocalization.map_units (Bcyc p) s).mul_left_eq_zero.mp hbs

end Universal

section Main

variable (p : ℕ) [hp : Fact p.Prime]

theorem field_case (hp5 : 5 ≤ p) :
    ((tateBase ℂ p).preΨ (p : ℤ)).eval (tateToricPoint ℂ p (ζℂu p)).1 = 0 := by
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have h := TateCurve.isRoot_prePsi_curve_pointX_laurentSeries ℂ p hodd hp5 (ζℂ p) (ζℂ_spec p) 1 0
    hp.out.one_lt hp.out.pos (by simp)
  rw [pow_one, pow_zero, mul_one, ModularCurve.tateCurve_curve_X_pow_eq_tateBase ℂ p,
    show (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (ζℂ p) = HahnSeries.C ((ζℂu p : ℂˣ) : ℂ) from rfl,
    ModularCurve.tateCurve_pointX_C_eq_tateToricPoint_fst ℂ p (ζℂu p) (ζℂ_ne_one p),
    ← WeierstrassCurve.preΨ_ofNat] at h
  exact h.eq_zero

theorem main (K : Type u) [CommRing K] (hp5 : 5 ≤ p) (c : Kˣ) (hc : c ^ p = 1) (h1c : IsUnit (1 - (c : K))) :
    ((tateBase K p).preΨ (p : ℤ)).eval (tateToricPoint K p c).1 = 0 := by
  have hc' : (c : K) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]

  have hB : ((tateBase (Bcyc p) p).preΨ (p : ℤ)).eval (tateToricPoint (Bcyc p) p (cB p)).1 = 0 := by
    apply coeffMap_injective (toC p) (toC_injective p)
    rw [map_zero, coeffMap_eval_preΨ (toC p) p (p : ℤ) (cB p) (isUnit_one_sub_cB p), toC_cB]
    exact field_case p hp5

  have h := congrArg (coeffMap (toRing p K c hc' h1c)) hB
  rwa [map_zero, coeffMap_eval_preΨ _ p _ _ (isUnit_one_sub_cB p), toRing_cB p K c hc h1c] at h

end Main

end ModularCurve.ToricTorsion
p2m_reactivate "P2MW.S_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le.ModularCurve P2MW.S_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le.ModularCurve.ToricTorsion"
p2m_reactivate "P2MW.S_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le.ModularCurve"

theorem solution
    (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (c : Kˣ) (hc : c ^ p = 1)
    (h1c : IsUnit (1 - (c : K))) :
    ((ModularCurve.tateBase K p).preΨ (p : ℤ)).eval (ModularCurve.tateToricPoint K p c).1 = 0 :=
  ModularCurve.ToricTorsion.main p K hp5 c hc h1c

end
p2m_reactivate "P2MW.S_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le.ModularCurve P2MW.S_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le.ModularCurve.ToricTorsion"

end S_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le
end P2MW
export P2MW.S_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le (solution)

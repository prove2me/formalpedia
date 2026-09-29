-- Prove2me | solution 1 for ModularCurve.equation_tateBase_nonToricPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4ab12755-f808-57bb-b566-dedb0ef255fb

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_nonToricPoint_equation
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivY
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_equation_tateBase_nonToricPoint
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_equation_tateBase_nonToricPoint.ModularCurve HahnSeries Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "tateUnivX tateUnivY slotSubst nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd laurentOfInt laurentOfInt_apply tateLaurent qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd coeffMap coeffMap_coeff nonToricPoint_equation coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace CuspTransfer
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

theorem coeffMap_injective (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem equation_of_map {W : WeierstrassCurve A} {x y : A} (hf : Function.Injective f)
    (h : (W.map f).toAffine.Equation (f x) (f y)) : W.toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  apply hf
  simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_add, map_mul, map_pow] using h

variable (p : ℕ) (c : Aˣ) (j : ℕ)

theorem map_slotSubst_tateUnivX (hj : 0 < j) (hjp : j < p) :
    PowerSeries.map f (slotSubst A p c j tateUnivX) =
      slotSubst B p (Units.map (f : A →* B) c) j tateUnivX := by
  ext n
  rw [PowerSeries.coeff_map, coeff_slotSubst_tateUnivX p c j hj hjp n,
    coeff_slotSubst_tateUnivX p (Units.map (f : A →* B) c) j hj hjp n]
  simp only [map_add, map_sub, map_sum, map_mul, map_pow, map_natCast, map_ofNat, map_zero,
    apply_ite f, Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

theorem map_slotSubst_tateUnivY (hj : 0 < j) (hjp : j < p) :
    PowerSeries.map f (slotSubst A p c j tateUnivY) =
      slotSubst B p (Units.map (f : A →* B) c) j tateUnivY := by
  ext n
  rw [PowerSeries.coeff_map, coeff_slotSubst_tateUnivY p c j hj hjp n,
    coeff_slotSubst_tateUnivY p (Units.map (f : A →* B) c) j hj hjp n]
  simp only [map_add, map_sub, map_sum, map_mul, map_pow, map_natCast, map_zero,
    apply_ite f, Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

theorem coeffMap_nonToricPoint_fst (hj : 0 < j) (hjp : j < p) :
    coeffMap f (nonToricPoint A p c j).1 = (nonToricPoint B p (Units.map (f : A →* B) c) j).1 := by
  rw [nonToricPoint_fst, nonToricPoint_fst, coeffMap_ofPowerSeries, map_slotSubst_tateUnivX f p c j hj hjp]

theorem coeffMap_nonToricPoint_snd (hj : 0 < j) (hjp : j < p) :
    coeffMap f (nonToricPoint A p c j).2 = (nonToricPoint B p (Units.map (f : A →* B) c) j).2 := by
  rw [nonToricPoint_snd, nonToricPoint_snd, coeffMap_ofPowerSeries, map_slotSubst_tateUnivY f p c j hj hjp]

end Naturality

section Universal

abbrev U : Type := Localization.Away (X : ℤ[X])

theorem isUnit_algebraMap_X : IsUnit (algebraMap ℤ[X] U X) :=
  IsLocalization.Away.algebraMap_isUnit X

noncomputable def cU : Uˣ := isUnit_algebraMap_X.unit

@[scoped simp] theorem val_cU : (cU : U) = algebraMap ℤ[X] U X := rfl

noncomputable def g₀ : ℤ[X] →+* RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem g₀_X : g₀ X = RatFunc.X := by
  simp [g₀, RatFunc.algebraMap_X]

theorem g₀_injective : Function.Injective g₀ :=
  (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).comp
    (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)

theorem isUnit_g₀_X : IsUnit (g₀ X) := by
  rw [g₀_X]; exact isUnit_iff_ne_zero.mpr RatFunc.X_ne_zero

noncomputable def ι : U →+* RatFunc ℚ := IsLocalization.Away.lift X isUnit_g₀_X

theorem ι_algebraMap (a : ℤ[X]) : ι (algebraMap ℤ[X] U a) = g₀ a :=
  IsLocalization.Away.lift_eq X isUnit_g₀_X a

theorem ι_injective : Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.mk'_surjective (Submonoid.powers (X : ℤ[X])) z
  dsimp only at e
  subst e
  have hs : IsUnit (ι (algebraMap ℤ[X] U s)) := by
    obtain ⟨n, hn⟩ := s.2
    rw [ι_algebraMap, ← hn, map_pow]
    exact isUnit_g₀_X.pow n
  have h1 : ι (IsLocalization.mk' U a s) * ι (algebraMap ℤ[X] U s) = g₀ a := by
    rw [← map_mul, IsLocalization.mk'_spec, ι_algebraMap]
  rw [hz, zero_mul] at h1
  have ha : a = 0 := g₀_injective (by rw [← h1, map_zero])
  rw [ha, IsLocalization.mk'_zero]

variable (K : Type*) [CommRing K] (c : Kˣ)

noncomputable def toK : U →+* K :=
  IsLocalization.Away.lift X (g := Polynomial.eval₂RingHom (Int.castRingHom K) (c : K))
    (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]; exact c.isUnit)

theorem toK_cU : Units.map (toK K c : U →* K) cU = c := by
  ext
  rw [Units.coe_map, MonoidHom.coe_coe, val_cU, toK, IsLocalization.Away.lift_eq,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

end Universal

theorem equation_universal (p : ℕ) [NeZero p] (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (tateBase U p).toAffine.Equation (nonToricPoint U p cU j).1 (nonToricPoint U p cU j).2 := by
  have hF := ModularCurve.nonToricPoint_equation (RatFunc ℚ) p (Units.map (ι : U →* RatFunc ℚ) cU) j hj hjp
  rw [← tateBase_map_coeffMap ι p, ← coeffMap_nonToricPoint_fst ι p cU j hj hjp,
    ← coeffMap_nonToricPoint_snd ι p cU j hj hjp] at hF
  exact equation_of_map (coeffMap ι) (coeffMap_injective ι ι_injective) hF

theorem equation_tateBase_nonToricPoint'
    (K : Type*) [CommRing K] (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (ModularCurve.tateBase K p).toAffine.Equation
      (ModularCurve.nonToricPoint K p c j).1 (ModularCurve.nonToricPoint K p c j).2 := by
  have h : ((ModularCurve.tateBase U p).map (coeffMap (toK K c))).toAffine.Equation
      (coeffMap (toK K c) (ModularCurve.nonToricPoint U p cU j).1)
      (coeffMap (toK K c) (ModularCurve.nonToricPoint U p cU j).2) :=
    (equation_universal p j hj hjp).map (coeffMap (toK K c))
  rwa [tateBase_map_coeffMap, coeffMap_nonToricPoint_fst _ p cU j hj hjp,
    coeffMap_nonToricPoint_snd _ p cU j hj hjp, toK_cU] at h

end ModularCurve.CuspTransfer
p2m_reactivate "P2MW.S_ModularCurve_equation_tateBase_nonToricPoint.ModularCurve P2MW.S_ModularCurve_equation_tateBase_nonToricPoint.ModularCurve.CuspTransfer"
p2m_reactivate "P2MW.S_ModularCurve_equation_tateBase_nonToricPoint.ModularCurve"

open ModularCurve.CuspTransfer in
theorem solution (K : Type*) [CommRing K] (p : ℕ)
    [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (tateBase K p).toAffine.Equation (nonToricPoint K p c j).1 (nonToricPoint K p c j).2 :=
  ModularCurve.CuspTransfer.equation_tateBase_nonToricPoint' K p c j hj hjp

end S_ModularCurve_equation_tateBase_nonToricPoint
end P2MW
export P2MW.S_ModularCurve_equation_tateBase_nonToricPoint (solution)

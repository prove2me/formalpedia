-- Prove2me | solution 1 for ModularCurve.equation_tateBase_tateToricPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/2043f7c9-472e-5b72-9101-2c1d01aac44c

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_toricPoint_equation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_equation_tateBase_tateToricPoint
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

universe u

p2m_open "ModularCurve P2MW.S_ModularCurve_equation_tateBase_tateToricPoint.ModularCurve HahnSeries Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "tateBase toricPoint laurentOfInt laurentOfInt_apply tateLaurent qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd coeffMap coeffMap_coeff tateToricPoint tateToricPoint_fst tateToricPoint_snd tateToricPoint_eq_toricPoint toricPoint_equation"
namespace ToricTransfer
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

theorem map_ringInverse {x : A} (hx : IsUnit x) : f (Ring.inverse x) = Ring.inverse (f x) := by
  obtain ⟨u, rfl⟩ := hx
  rw [Ring.inverse_unit, show f (u : A) = ((Units.map (f : A →* B) u : Bˣ) : B) from rfl,
    Ring.inverse_unit, Units.coe_map_inv, MonoidHom.coe_coe]

variable (p : ℕ) (c : Aˣ)

theorem coeffMap_tateToricPoint_fst (hc : IsUnit (1 - (c : A))) :
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

theorem coeffMap_tateToricPoint_snd (hc : IsUnit (1 - (c : A))) :
    coeffMap f (tateToricPoint A p c).2 = (tateToricPoint B p (Units.map (f : A →* B) c)).2 := by
  have h1 : f (Ring.inverse (1 - (c : A))) = Ring.inverse (1 - ((Units.map (f : A →* B) c : Bˣ) : B)) := by
    rw [map_ringInverse f hc, map_sub, map_one, Units.coe_map, MonoidHom.coe_coe]
  rw [tateToricPoint_snd, tateToricPoint_snd, coeffMap_ofPowerSeries]
  congr 1
  ext m
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm, map_mul, map_pow, map_pow, h1, Units.coe_map, MonoidHom.coe_coe]
  · rw [if_neg hm, if_neg hm]
    simp only [map_add, map_sub, map_sum, map_mul, map_pow, map_natCast, map_zero,
      apply_ite f, Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

end Naturality

section Universal

noncomputable abbrev d : ℤ[X] := X * (1 - X)

abbrev U : Type := Localization.Away d

theorem isUnit_algebraMap_d : IsUnit (algebraMap ℤ[X] U d) :=
  IsLocalization.Away.algebraMap_isUnit d

theorem isUnit_algebraMap_X : IsUnit (algebraMap ℤ[X] U X) :=
  isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact isUnit_algebraMap_d)

noncomputable def cU : Uˣ := isUnit_algebraMap_X.unit

@[scoped simp] theorem val_cU : (cU : U) = algebraMap ℤ[X] U X := rfl

theorem isUnit_one_sub_cU : IsUnit (1 - (cU : U)) := by
  rw [val_cU, ← map_one (algebraMap ℤ[X] U), ← map_sub]
  exact isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact isUnit_algebraMap_d)

noncomputable def g₀ : ℤ[X] →+* RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem g₀_injective : Function.Injective g₀ :=
  (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).comp
    (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)

theorem isUnit_g₀_d : IsUnit (g₀ d) := by
  rw [isUnit_iff_ne_zero, map_ne_zero_iff g₀ g₀_injective]
  exact mul_ne_zero Polynomial.X_ne_zero (by
    rw [sub_ne_zero]; intro h
    have := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_one, Polynomial.natDegree_X] at this
    exact zero_ne_one this)

noncomputable def ι : U →+* RatFunc ℚ := IsLocalization.Away.lift d isUnit_g₀_d

theorem ι_algebraMap (a : ℤ[X]) : ι (algebraMap ℤ[X] U a) = g₀ a :=
  IsLocalization.Away.lift_eq d isUnit_g₀_d a

theorem ι_injective : Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.mk'_surjective (Submonoid.powers d) z
  dsimp only at e
  subst e
  have h1 : ι (IsLocalization.mk' U a s) * ι (algebraMap ℤ[X] U s) = g₀ a := by
    rw [← map_mul, IsLocalization.mk'_spec, ι_algebraMap]
  rw [hz, zero_mul] at h1
  have ha : a = 0 := g₀_injective (by rw [← h1, map_zero])
  rw [ha, IsLocalization.mk'_zero]

variable (K : Type*) [CommRing K] (c : Kˣ) (hc : IsUnit (1 - (c : K)))

noncomputable def toK : U →+* K :=
  IsLocalization.Away.lift d (g := Polynomial.eval₂RingHom (Int.castRingHom K) (c : K))
    (by
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_sub,
        Polynomial.eval₂_one, Polynomial.eval₂_X]
      exact c.isUnit.mul hc)

theorem toK_cU : Units.map (toK K c hc : U →* K) cU = c := by
  ext
  rw [Units.coe_map, MonoidHom.coe_coe, val_cU, toK, IsLocalization.Away.lift_eq,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

end Universal

theorem equation_ratFunc (p : ℕ) [NeZero p] :
    (tateBase (RatFunc ℚ) p).toAffine.Equation
      (tateToricPoint (RatFunc ℚ) p (Units.map (ι : U →* RatFunc ℚ) cU)).1
      (tateToricPoint (RatFunc ℚ) p (Units.map (ι : U →* RatFunc ℚ) cU)).2 := by
  set cF : (RatFunc ℚ)ˣ := Units.map (ι : U →* RatFunc ℚ) cU
  have hc1 : (cF : RatFunc ℚ) ≠ 1 := by
    intro h
    have hu : IsUnit (1 - (cF : RatFunc ℚ)) := by
      have := isUnit_one_sub_cU.map ι
      rwa [map_sub, map_one] at this
    rw [h, sub_self] at hu
    exact not_isUnit_zero hu
  rw [tateToricPoint_eq_toricPoint]
  exact ModularCurve.toricPoint_equation (RatFunc ℚ) p (cF : RatFunc ℚ) cF.ne_zero hc1

theorem equation_universal (p : ℕ) [NeZero p] :
    (tateBase U p).toAffine.Equation (tateToricPoint U p cU).1 (tateToricPoint U p cU).2 := by
  have hF := equation_ratFunc p
  rw [← tateBase_map_coeffMap ι p, ← coeffMap_tateToricPoint_fst ι p cU isUnit_one_sub_cU,
    ← coeffMap_tateToricPoint_snd ι p cU isUnit_one_sub_cU] at hF
  exact equation_of_map (coeffMap ι) (coeffMap_injective ι ι_injective) hF

theorem equation_main
    (K : Type*) [CommRing K] (p : ℕ) [NeZero p] (c : Kˣ) (hc : IsUnit (1 - (c : K))) :
    (ModularCurve.tateBase K p).toAffine.Equation
      (ModularCurve.tateToricPoint K p c).1 (ModularCurve.tateToricPoint K p c).2 := by
  have h : ((ModularCurve.tateBase U p).map (coeffMap (toK K c hc))).toAffine.Equation
      (coeffMap (toK K c hc) (ModularCurve.tateToricPoint U p cU).1)
      (coeffMap (toK K c hc) (ModularCurve.tateToricPoint U p cU).2) :=
    (equation_universal p).map (coeffMap (toK K c hc))
  rwa [tateBase_map_coeffMap, coeffMap_tateToricPoint_fst _ p cU isUnit_one_sub_cU,
    coeffMap_tateToricPoint_snd _ p cU isUnit_one_sub_cU, toK_cU] at h

end ModularCurve.ToricTransfer
p2m_reactivate "P2MW.S_ModularCurve_equation_tateBase_tateToricPoint.ModularCurve P2MW.S_ModularCurve_equation_tateBase_tateToricPoint.ModularCurve.ToricTransfer"
p2m_reactivate "P2MW.S_ModularCurve_equation_tateBase_tateToricPoint.ModularCurve"

open ModularCurve.ToricTransfer in
theorem solution
    (K : Type u) [CommRing K] (p : ℕ) [NeZero p] (c : Kˣ) (hc : IsUnit (1 - (c : K))) :
    (ModularCurve.tateBase K p).toAffine.Equation
      (ModularCurve.tateToricPoint K p c).1 (ModularCurve.tateToricPoint K p c).2 :=
  ModularCurve.ToricTransfer.equation_main K p c hc

end S_ModularCurve_equation_tateBase_tateToricPoint
end P2MW
export P2MW.S_ModularCurve_equation_tateBase_tateToricPoint (solution)

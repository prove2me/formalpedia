-- Prove2me | solution 1 for ModularCurve.exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f099d1ce-be8b-5644-8b65-2f76a5467f3f

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_toricPoint_add_toricPoint_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace ModularCurve
p2m_export "ModularCurve" "toricPoint toricPoint_fst toricPoint_snd tatePowerSeries laurentOfInt laurentOfInt_apply tateLaurent tateToricPoint tateToricPoint_fst tateToricPoint_snd tateToricPoint_eq_toricPoint coeffMap coeffMap_coeff toricPoint_add_toricPoint_of_charZero"
p2m_open "ModularCurve"

namespace P2MToricLevel

universe u v

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem coeffMap_ofPowerSeries (φ : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R φ) = HahnSeries.ofPowerSeries ℤ S (φ.map f) := by
  ext n
  rw [coeffMap_coeff]
  change f (((φ : PowerSeries R) : LaurentSeries R).coeff n) =
    ((PowerSeries.map f φ : PowerSeries S) : LaurentSeries S).coeff n
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · exact map_zero f
  · exact (PowerSeries.coeff_map _ _ _).symm

theorem coeffMap_laurentOfInt (φ : PowerSeries ℤ) :
    coeffMap f (laurentOfInt R φ) = laurentOfInt S φ := by
  rw [laurentOfInt_apply, laurentOfInt_apply, coeffMap_ofPowerSeries,
    ← RingHom.comp_apply (PowerSeries.map f) (PowerSeries.map (Int.castRingHom R)),
    ← PowerSeries.map_comp, RingHom.ext_int (f.comp (Int.castRingHom R)) (Int.castRingHom S)]

theorem tateLaurent_map : (tateLaurent R).map (coeffMap f) = tateLaurent S := by
  rw [tateLaurent, tateLaurent, WeierstrassCurve.map_map]
  congr 1
  exact RingHom.ext fun φ => coeffMap_laurentOfInt f φ

theorem coeffMap_injective (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem map_ringInverse_one_sub {c : R} (h : IsUnit (1 - c)) :
    f (Ring.inverse (1 - c)) = Ring.inverse (1 - f c) := by
  obtain ⟨u, hu⟩ := h
  have hu' : ((Units.map (f : R →* S) u : Sˣ) : S) = 1 - f c := by
    rw [Units.coe_map, MonoidHom.coe_coe, hu, map_sub, map_one]
  rw [← hu, Ring.inverse_unit, ← hu', Ring.inverse_unit, Units.coe_map_inv, MonoidHom.coe_coe]

theorem coeffMap_tateToricPoint_fst (p : ℕ) (c : Rˣ) (h1 : IsUnit (1 - (c : R))) :
    coeffMap f (tateToricPoint R p c).1 = (tateToricPoint S p (Units.map (f : R →* S) c)).1 := by
  rw [tateToricPoint_fst, tateToricPoint_fst, coeffMap_ofPowerSeries]
  congr 1
  ext m
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm, map_mul, map_pow, map_ringInverse_one_sub f h1, Units.coe_map,
      MonoidHom.coe_coe]
  · rw [if_neg hm, if_neg hm]
    simp only [map_sub, map_sum, map_mul, map_add, map_pow, map_natCast, apply_ite f, map_zero,
      map_ofNat, Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

theorem coeffMap_tateToricPoint_snd (p : ℕ) (c : Rˣ) (h1 : IsUnit (1 - (c : R))) :
    coeffMap f (tateToricPoint R p c).2 = (tateToricPoint S p (Units.map (f : R →* S) c)).2 := by
  rw [tateToricPoint_snd, tateToricPoint_snd, coeffMap_ofPowerSeries]
  congr 1
  ext m
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm, map_mul, map_pow, map_pow, map_ringInverse_one_sub f h1,
      Units.coe_map, MonoidHom.coe_coe]
  · rw [if_neg hm, if_neg hm]
    simp only [map_sub, map_sum, map_mul, map_add, map_pow, map_natCast, apply_ite f, map_zero,
      Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

end Transport

section Relations

variable {S T : Type*} [CommRing S] [CommRing T]

def negRel (W : WeierstrassCurve S) (x y x' y' : S) : Prop :=
  x' = x ∧ y' = W.toAffine.negY x y

def chordRel (W : WeierstrassCurve S) (x₁ y₁ x₂ y₂ x₃ y₃ : S) : Prop :=
  (x₁ - x₂) ^ 2 * x₃ =
      (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) - (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2 ∧
  (x₁ - x₂) * y₃ = -((y₁ - y₂) * (x₃ - x₁)) - (x₁ - x₂) * y₁ - (x₁ - x₂) * (W.a₁ * x₃ + W.a₃)

def dblRel (W : WeierstrassCurve S) (x₁ y₁ x₃ y₃ : S) : Prop :=
  (2 * y₁ + W.a₁ * x₁ + W.a₃) ^ 2 * x₃ =
      (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) ^ 2
        + W.a₁ * (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) * (2 * y₁ + W.a₁ * x₁ + W.a₃)
        - (W.a₂ + x₁ + x₁) * (2 * y₁ + W.a₁ * x₁ + W.a₃) ^ 2 ∧
  (2 * y₁ + W.a₁ * x₁ + W.a₃) * y₃ =
      -((3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) * (x₃ - x₁))
        - (2 * y₁ + W.a₁ * x₁ + W.a₃) * y₁ - (2 * y₁ + W.a₁ * x₁ + W.a₃) * (W.a₁ * x₃ + W.a₃)

variable (f : S →+* T) (W : WeierstrassCurve S)

theorem negRel_map {x y x' y' : S} (h : negRel W x y x' y') :
    negRel (W.map f) (f x) (f y) (f x') (f y') := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by rw [h1], by rw [h2, map_negY]⟩

theorem negRel_of_map (hf : Function.Injective f) {x y x' y' : S}
    (h : negRel (W.map f) (f x) (f y) (f x') (f y')) : negRel W x y x' y' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨hf h1, hf ?_⟩
  rw [h2, map_negY]

theorem chordRel_map {x₁ y₁ x₂ y₂ x₃ y₃ : S} (h : chordRel W x₁ y₁ x₂ y₂ x₃ y₃) :
    chordRel (W.map f) (f x₁) (f y₁) (f x₂) (f y₂) (f x₃) (f y₃) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have := congrArg f h1
    simpa only [map_mul, map_sub, map_add, map_pow, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂] using this
  · have := congrArg f h2
    simpa only [map_mul, map_sub, map_add, map_neg, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃] using this

theorem chordRel_of_map (hf : Function.Injective f) {x₁ y₁ x₂ y₂ x₃ y₃ : S}
    (h : chordRel (W.map f) (f x₁) (f y₁) (f x₂) (f y₂) (f x₃) (f y₃)) :
    chordRel W x₁ y₁ x₂ y₂ x₃ y₃ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨hf ?_, hf ?_⟩
  · simpa only [map_mul, map_sub, map_add, map_pow, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂] using h1
  · simpa only [map_mul, map_sub, map_add, map_neg, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃] using h2

theorem dblRel_map {x₁ y₁ x₃ y₃ : S} (h : dblRel W x₁ y₁ x₃ y₃) :
    dblRel (W.map f) (f x₁) (f y₁) (f x₃) (f y₃) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have := congrArg f h1
    simpa only [map_mul, map_sub, map_add, map_pow, map_ofNat, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄] using this
  · have := congrArg f h2
    simpa only [map_mul, map_sub, map_add, map_neg, map_pow, map_ofNat, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄] using this

theorem dblRel_of_map (hf : Function.Injective f) {x₁ y₁ x₃ y₃ : S}
    (h : dblRel (W.map f) (f x₁) (f y₁) (f x₃) (f y₃)) : dblRel W x₁ y₁ x₃ y₃ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨hf ?_, hf ?_⟩
  · simpa only [map_mul, map_sub, map_add, map_pow, map_ofNat, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄] using h1
  · simpa only [map_mul, map_sub, map_add, map_neg, map_pow, map_ofNat, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄] using h2

end Relations

theorem point_some_congr {R' : Type*} [CommRing R'] {W : WeierstrassCurve R'} {x x' y y' : R'}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

section FieldRelations

variable {E : Type*} [Field E] [DecidableEq E] {W : WeierstrassCurve E}

theorem negRel_of_add_eq_zero {x₁ y₁ x₂ y₂ : E} {h₁ : W.toAffine.Nonsingular x₁ y₁}
    {h₂ : W.toAffine.Nonsingular x₂ y₂}
    (h : (Point.some x₁ y₁ h₁ : W.toAffine.Point) + Point.some x₂ y₂ h₂ = 0) :
    negRel W x₁ y₁ x₂ y₂ := by
  rw [add_comm, add_eq_zero_iff_eq_neg, Point.neg_some] at h
  simp only [Point.some.injEq] at h
  exact ⟨h.1, h.2⟩

theorem chordRel_of_add_eq {x₁ y₁ x₂ y₂ x₃ y₃ : E} {h₁ : W.toAffine.Nonsingular x₁ y₁}
    {h₂ : W.toAffine.Nonsingular x₂ y₂} {h₃ : W.toAffine.Nonsingular x₃ y₃}
    (h : (Point.some x₁ y₁ h₁ : W.toAffine.Point) + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃)
    (hx : x₁ ≠ x₂) : chordRel W x₁ y₁ x₂ y₂ x₃ y₃ := by
  rw [Point.add_of_X_ne hx] at h
  simp only [Point.some.injEq] at h
  obtain ⟨hx3, hy3⟩ := h
  have hδ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  set L := W.toAffine.slope x₁ x₂ y₁ y₂ with hLdef
  have hL : L * (x₁ - x₂) = y₁ - y₂ := by
    rw [hLdef, slope_of_X_ne hx, div_mul_cancel₀ _ hδ]
  refine ⟨?_, ?_⟩
  · rw [← hx3]
    simp only [addX]
    linear_combination ((x₁ - x₂) * L + (y₁ - y₂) + W.a₁ * (x₁ - x₂)) * hL
  · rw [← hy3]
    simp only [addY, negAddY, negY]
    rw [hx3]
    linear_combination (-(x₃ - x₁)) * hL

theorem dblRel_of_add_self_eq {x₁ y₁ x₃ y₃ : E} {h₁ : W.toAffine.Nonsingular x₁ y₁}
    {h₃ : W.toAffine.Nonsingular x₃ y₃}
    (h : (Point.some x₁ y₁ h₁ : W.toAffine.Point) + Point.some x₁ y₁ h₁ = Point.some x₃ y₃ h₃) :
    dblRel W x₁ y₁ x₃ y₃ := by
  have hy : y₁ ≠ W.toAffine.negY x₁ y₁ := by
    intro hy
    rw [Point.add_self_of_Y_eq hy] at h
    exact (Point.some_ne_zero h₃) h.symm
  rw [Point.add_self_of_Y_ne hy] at h
  simp only [Point.some.injEq] at h
  obtain ⟨hx3, hy3⟩ := h
  have hδ' : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
  have hδeq : y₁ - W.toAffine.negY x₁ y₁ = 2 * y₁ + W.a₁ * x₁ + W.a₃ := by
    simp only [negY]; ring
  have hδ : 2 * y₁ + W.a₁ * x₁ + W.a₃ ≠ 0 := by rwa [hδeq] at hδ'
  set L := W.toAffine.slope x₁ x₁ y₁ y₁ with hLdef
  have hL : L * (2 * y₁ + W.a₁ * x₁ + W.a₃) = 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ := by
    rw [hLdef, slope_of_Y_ne rfl hy, hδeq, div_mul_cancel₀ _ hδ]
  refine ⟨?_, ?_⟩
  · rw [← hx3]
    simp only [addX]
    linear_combination ((2 * y₁ + W.a₁ * x₁ + W.a₃) * L
      + (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) + W.a₁ * (2 * y₁ + W.a₁ * x₁ + W.a₃)) * hL
  · rw [← hy3]
    simp only [addY, negAddY, negY]
    rw [hx3]
    linear_combination (-(x₃ - x₁)) * hL

theorem add_eq_of_chordRel {x₁ y₁ x₂ y₂ x₃ y₃ : E} (h : chordRel W x₁ y₁ x₂ y₂ x₃ y₃)
    (hx : x₁ ≠ x₂) (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (h₃ : W.toAffine.Nonsingular x₃ y₃) :
    (Point.some x₁ y₁ h₁ : W.toAffine.Point) + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ := by
  obtain ⟨c1, c2⟩ := h
  rw [Point.add_of_X_ne hx]
  have hδ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  set L := W.toAffine.slope x₁ x₂ y₁ y₂ with hLdef
  have hL : L * (x₁ - x₂) = y₁ - y₂ := by
    rw [hLdef, slope_of_X_ne hx, div_mul_cancel₀ _ hδ]
  have hx3 : W.toAffine.addX x₁ x₂ L = x₃ := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hδ)
    rw [c1]
    simp only [addX]
    linear_combination ((x₁ - x₂) * L + (y₁ - y₂) + W.a₁ * (x₁ - x₂)) * hL
  have hy3 : W.toAffine.addY x₁ x₂ y₁ L = y₃ := by
    apply mul_left_cancel₀ hδ
    rw [c2]
    simp only [addY, negAddY, negY]
    rw [hx3]
    linear_combination (-(x₃ - x₁)) * hL
  exact point_some_congr hx3 hy3 _ _

theorem add_eq_of_dblRel {x₁ y₁ x₃ y₃ : E} (h : dblRel W x₁ y₁ x₃ y₃)
    (hy : y₁ ≠ W.toAffine.negY x₁ y₁) (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₃ : W.toAffine.Nonsingular x₃ y₃) :
    (Point.some x₁ y₁ h₁ : W.toAffine.Point) + Point.some x₁ y₁ h₁ = Point.some x₃ y₃ h₃ := by
  obtain ⟨c1, c2⟩ := h
  rw [Point.add_self_of_Y_ne hy]
  have hδ' : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
  have hδeq : y₁ - W.toAffine.negY x₁ y₁ = 2 * y₁ + W.a₁ * x₁ + W.a₃ := by
    simp only [negY]; ring
  have hδ : 2 * y₁ + W.a₁ * x₁ + W.a₃ ≠ 0 := by rwa [hδeq] at hδ'
  set L := W.toAffine.slope x₁ x₁ y₁ y₁ with hLdef
  have hL : L * (2 * y₁ + W.a₁ * x₁ + W.a₃) = 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ := by
    rw [hLdef, slope_of_Y_ne rfl hy, hδeq, div_mul_cancel₀ _ hδ]
  have hx3 : W.toAffine.addX x₁ x₁ L = x₃ := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hδ)
    rw [c1]
    simp only [addX]
    linear_combination ((2 * y₁ + W.a₁ * x₁ + W.a₃) * L
      + (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) + W.a₁ * (2 * y₁ + W.a₁ * x₁ + W.a₃)) * hL
  have hy3 : W.toAffine.addY x₁ x₁ y₁ L = y₃ := by
    apply mul_left_cancel₀ hδ
    rw [c2]
    simp only [addY, negAddY, negY]
    rw [hx3]
    linear_combination (-(x₃ - x₁)) * hL
  exact point_some_congr hx3 hy3 _ _

end FieldRelations

section Ring

variable (K : Type u) [Field K] (ζ : K)

def ev : ℤ[X] →+* K := Polynomial.eval₂RingHom (Int.castRingHom K) ζ

def pz : Ideal ℤ[X] := RingHom.ker (ev K ζ)

scoped instance pz_isPrime : (pz K ζ).IsPrime := RingHom.ker_isPrime _

def Rz : Type := Localization.AtPrime (pz K ζ)

scoped instance commRing_Rz : CommRing (Rz K ζ) := inferInstanceAs (CommRing (Localization.AtPrime (pz K ζ)))

scoped instance isDomain_Rz : IsDomain (Rz K ζ) := inferInstanceAs (IsDomain (Localization.AtPrime (pz K ζ)))

scoped instance algebra_Rz : Algebra ℤ[X] (Rz K ζ) :=
  inferInstanceAs (Algebra ℤ[X] (Localization.AtPrime (pz K ζ)))

scoped instance isLocalization_Rz : IsLocalization.AtPrime (Rz K ζ) (pz K ζ) :=
  inferInstanceAs (IsLocalization.AtPrime (Localization.AtPrime (pz K ζ)) (pz K ζ))

theorem mem_primeCompl {g : ℤ[X]} (hg : ev K ζ g ≠ 0) : g ∈ (pz K ζ).primeCompl := by
  rw [Ideal.mem_primeCompl_iff]
  exact fun h => hg ((RingHom.mem_ker).mp h)

def spec : Rz K ζ →+* K :=
  IsLocalization.lift (M := (pz K ζ).primeCompl) (S := Rz K ζ) (g := ev K ζ)
    (fun y => isUnit_iff_ne_zero.mpr fun h =>
      (Ideal.mem_primeCompl_iff.mp y.2) ((RingHom.mem_ker).mpr h))

theorem spec_algebraMap (g : ℤ[X]) : spec K ζ (algebraMap ℤ[X] (Rz K ζ) g) = ev K ζ g :=
  IsLocalization.lift_eq _ g

theorem algebraMap_injective : Function.Injective (algebraMap ℤ[X] (Rz K ζ)) :=
  IsLocalization.injective (Rz K ζ) (pz K ζ).primeCompl_le_nonZeroDivisors

scoped instance charZero_Rz : CharZero (Rz K ζ) :=
  charZero_of_injective_ringHom (algebraMap_injective K ζ)

def Fz : Type := FractionRing (Rz K ζ)

scoped instance field_Fz : Field (Fz K ζ) := inferInstanceAs (Field (FractionRing (Rz K ζ)))

scoped instance algebra_Fz : Algebra (Rz K ζ) (Fz K ζ) :=
  inferInstanceAs (Algebra (Rz K ζ) (FractionRing (Rz K ζ)))

scoped instance isFractionRing_Fz : IsFractionRing (Rz K ζ) (Fz K ζ) :=
  inferInstanceAs (IsFractionRing (Rz K ζ) (FractionRing (Rz K ζ)))

scoped instance charZero_Fz : CharZero (Fz K ζ) :=
  charZero_of_injective_ringHom (IsFractionRing.injective (Rz K ζ) (Fz K ζ))

def unitOf (g : ℤ[X]) (hg : ev K ζ g ≠ 0) : (Rz K ζ)ˣ :=
  (IsLocalization.map_units (Rz K ζ) (⟨g, mem_primeCompl K ζ hg⟩ : (pz K ζ).primeCompl)).unit

theorem val_unitOf (g : ℤ[X]) (hg : ev K ζ g ≠ 0) :
    ((unitOf K ζ g hg : (Rz K ζ)ˣ) : Rz K ζ) = algebraMap ℤ[X] (Rz K ζ) g :=
  IsUnit.unit_spec _

theorem spec_unitOf (g : ℤ[X]) (hg : ev K ζ g ≠ 0) :
    spec K ζ (unitOf K ζ g hg : (Rz K ζ)ˣ) = ev K ζ g := by
  rw [val_unitOf, spec_algebraMap]

theorem isUnit_algebraMap {g : ℤ[X]} (hg : ev K ζ g ≠ 0) :
    IsUnit (algebraMap ℤ[X] (Rz K ζ) g) :=
  IsLocalization.map_units (Rz K ζ) (⟨g, mem_primeCompl K ζ hg⟩ : (pz K ζ).primeCompl)

variable {ζ}

def cX (hζ0 : ζ ≠ 0) (n : ℕ) : (Rz K ζ)ˣ :=
  unitOf K ζ (X ^ n) (by
    show Polynomial.eval₂ (Int.castRingHom K) ζ (X ^ n) ≠ 0
    rw [eval₂_X_pow]; exact pow_ne_zero n hζ0)

theorem val_cX (hζ0 : ζ ≠ 0) (n : ℕ) :
    ((cX K hζ0 n : (Rz K ζ)ˣ) : Rz K ζ) = algebraMap ℤ[X] (Rz K ζ) X ^ n := by
  rw [cX, val_unitOf, map_pow]

theorem spec_cX (hζ0 : ζ ≠ 0) (n : ℕ) : spec K ζ (cX K hζ0 n : (Rz K ζ)ˣ) = ζ ^ n := by
  rw [cX, spec_unitOf]
  show Polynomial.eval₂ (Int.castRingHom K) ζ (X ^ n) = ζ ^ n
  rw [eval₂_X_pow]

theorem cX_mul (hζ0 : ζ ≠ 0) (m n : ℕ) : cX K hζ0 m * cX K hζ0 n = cX K hζ0 (m + n) := by
  ext; rw [Units.val_mul, val_cX, val_cX, val_cX, pow_add]

theorem map_spec_cX (hζ0 : ζ ≠ 0) (n : ℕ) :
    Units.map (spec K ζ : Rz K ζ →* K) (cX K hζ0 n) = Units.mk0 (ζ ^ n) (pow_ne_zero n hζ0) := by
  ext; rw [Units.coe_map, MonoidHom.coe_coe, spec_cX, Units.val_mk0]

theorem map_spec_cX_inv (hζ0 : ζ ≠ 0) (n : ℕ) :
    Units.map (spec K ζ : Rz K ζ →* K) (cX K hζ0 n)⁻¹
      = Units.mk0 ((ζ ^ n)⁻¹) (inv_ne_zero (pow_ne_zero n hζ0)) := by
  rw [map_inv, map_spec_cX]; ext; rw [Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0]

theorem isUnit_one_sub_cX (hζ0 : ζ ≠ 0) {n : ℕ} (hn : ζ ^ n ≠ 1) :
    IsUnit (1 - ((cX K hζ0 n : (Rz K ζ)ˣ) : Rz K ζ)) := by
  have h : (1 : Rz K ζ) - ((cX K hζ0 n : (Rz K ζ)ˣ) : Rz K ζ) = algebraMap ℤ[X] (Rz K ζ) (1 - X ^ n) := by
    rw [val_cX, map_sub, map_one, map_pow]
  rw [h]
  refine isUnit_algebraMap K ζ ?_
  show Polynomial.eval₂ (Int.castRingHom K) ζ (1 - X ^ n) ≠ 0
  rw [eval₂_sub, eval₂_one, eval₂_X_pow]
  exact fun h0 => hn (sub_eq_zero.mp h0).symm

theorem isUnit_one_sub_cX_inv (hζ0 : ζ ≠ 0) {n : ℕ} (hn : ζ ^ n ≠ 1) :
    IsUnit (1 - ((cX K hζ0 n)⁻¹ : (Rz K ζ)ˣ) : Rz K ζ) := by
  have hu := isUnit_one_sub_cX K hζ0 hn

  have hinv : (((cX K hζ0 n)⁻¹ : (Rz K ζ)ˣ) : Rz K ζ) * ((cX K hζ0 n : (Rz K ζ)ˣ) : Rz K ζ) = 1 :=
    Units.inv_mul _
  have h : (1 : Rz K ζ) - ((cX K hζ0 n)⁻¹ : (Rz K ζ)ˣ)
      = -(((cX K hζ0 n)⁻¹ : (Rz K ζ)ˣ) : Rz K ζ) * (1 - ((cX K hζ0 n : (Rz K ζ)ˣ) : Rz K ζ)) := by
    linear_combination -hinv
  rw [h]
  exact ((Units.isUnit _).neg).mul hu

theorem cX_ne_one (hζ0 : ζ ≠ 0) {n : ℕ} (hn : ζ ^ n ≠ 1) :
    ((cX K hζ0 n : (Rz K ζ)ˣ) : Rz K ζ) ≠ 1 := by
  intro h
  apply hn
  rw [← spec_cX K hζ0 n, h, map_one]

end Ring

section Toric

variable (K : Type u) [Field K] {ζ : K}

theorem coeffMap_spec_toric_fst (hζ0 : ζ ≠ 0) {n : ℕ} (hn : ζ ^ n ≠ 1) :
    coeffMap (spec K ζ) (tateToricPoint (Rz K ζ) 1 (cX K hζ0 n)).1 = (toricPoint K 1 (ζ ^ n)).1 := by
  rw [coeffMap_tateToricPoint_fst _ 1 _ (isUnit_one_sub_cX K hζ0 hn), map_spec_cX,
    tateToricPoint_eq_toricPoint, Units.val_mk0]

theorem coeffMap_spec_toric_snd (hζ0 : ζ ≠ 0) {n : ℕ} (hn : ζ ^ n ≠ 1) :
    coeffMap (spec K ζ) (tateToricPoint (Rz K ζ) 1 (cX K hζ0 n)).2 = (toricPoint K 1 (ζ ^ n)).2 := by
  rw [coeffMap_tateToricPoint_snd _ 1 _ (isUnit_one_sub_cX K hζ0 hn), map_spec_cX,
    tateToricPoint_eq_toricPoint, Units.val_mk0]

theorem coeffMap_spec_toric_inv_fst (hζ0 : ζ ≠ 0) {n : ℕ} (hn : ζ ^ n ≠ 1) :
    coeffMap (spec K ζ) (tateToricPoint (Rz K ζ) 1 (cX K hζ0 n)⁻¹).1
      = (toricPoint K 1 (ζ ^ n)⁻¹).1 := by
  rw [coeffMap_tateToricPoint_fst _ 1 _ (isUnit_one_sub_cX_inv K hζ0 hn), map_spec_cX_inv,
    tateToricPoint_eq_toricPoint, Units.val_mk0]

theorem coeffMap_spec_toric_inv_snd (hζ0 : ζ ≠ 0) {n : ℕ} (hn : ζ ^ n ≠ 1) :
    coeffMap (spec K ζ) (tateToricPoint (Rz K ζ) 1 (cX K hζ0 n)⁻¹).2
      = (toricPoint K 1 (ζ ^ n)⁻¹).2 := by
  rw [coeffMap_tateToricPoint_snd _ 1 _ (isUnit_one_sub_cX_inv K hζ0 hn), map_spec_cX_inv,
    tateToricPoint_eq_toricPoint, Units.val_mk0]

theorem coeffMap_frac_toric_fst (c : (Rz K ζ)ˣ) (h1 : IsUnit (1 - (c : Rz K ζ))) :
    coeffMap (algebraMap (Rz K ζ) (Fz K ζ)) (tateToricPoint (Rz K ζ) 1 c).1
      = (toricPoint (Fz K ζ) 1 (algebraMap (Rz K ζ) (Fz K ζ) c)).1 := by
  rw [coeffMap_tateToricPoint_fst _ 1 _ h1, tateToricPoint_eq_toricPoint, Units.coe_map,
    MonoidHom.coe_coe]

theorem coeffMap_frac_toric_snd (c : (Rz K ζ)ˣ) (h1 : IsUnit (1 - (c : Rz K ζ))) :
    coeffMap (algebraMap (Rz K ζ) (Fz K ζ)) (tateToricPoint (Rz K ζ) 1 c).2
      = (toricPoint (Fz K ζ) 1 (algebraMap (Rz K ζ) (Fz K ζ) c)).2 := by
  rw [coeffMap_tateToricPoint_snd _ 1 _ h1, tateToricPoint_eq_toricPoint, Units.coe_map,
    MonoidHom.coe_coe]

theorem relations_R_one (c : (Rz K ζ)ˣ) (h1c : IsUnit (1 - (c : Rz K ζ)))
    (h1ci : IsUnit (1 - ((c⁻¹ : (Rz K ζ)ˣ) : Rz K ζ))) (hc1 : (c : Rz K ζ) ≠ 1) :
    (tateLaurent (Rz K ζ)).toAffine.Equation (tateToricPoint (Rz K ζ) 1 c).1
        (tateToricPoint (Rz K ζ) 1 c).2 ∧
    negRel (tateLaurent (Rz K ζ)) (tateToricPoint (Rz K ζ) 1 c).1 (tateToricPoint (Rz K ζ) 1 c).2
        (tateToricPoint (Rz K ζ) 1 c⁻¹).1 (tateToricPoint (Rz K ζ) 1 c⁻¹).2 := by
  classical
  let ι : Rz K ζ →+* Fz K ζ := algebraMap (Rz K ζ) (Fz K ζ)
  let ιL : LaurentSeries (Rz K ζ) →+* LaurentSeries (Fz K ζ) := coeffMap ι
  have hιinj : Function.Injective ι := IsFractionRing.injective (Rz K ζ) (Fz K ζ)
  have hιLinj : Function.Injective ιL := coeffMap_injective ι hιinj
  have hW : (tateLaurent (Rz K ζ)).map ιL = tateLaurent (Fz K ζ) := tateLaurent_map ι
  have hne0 : ∀ u : (Rz K ζ)ˣ, ι u ≠ 0 := fun u => (map_ne_zero_iff ι hιinj).mpr u.ne_zero
  have hne1 : ∀ {u : (Rz K ζ)ˣ}, (u : Rz K ζ) ≠ 1 → ι u ≠ 1 := fun hu h =>
    hu (hιinj (h.trans (map_one ι).symm))
  have hci1 : ((c⁻¹ : (Rz K ζ)ˣ) : Rz K ζ) ≠ 1 := by
    intro h; apply hc1
    have h2 : c⁻¹ = 1 := Units.ext h
    rw [← inv_inv c, h2, inv_one, Units.val_one]
  have hx : ∀ (u : (Rz K ζ)ˣ), IsUnit (1 - (u : Rz K ζ)) →
      ιL (tateToricPoint (Rz K ζ) 1 u).1 = (toricPoint (Fz K ζ) 1 (ι u)).1 := fun u hu =>
    coeffMap_frac_toric_fst K u hu
  have hy : ∀ (u : (Rz K ζ)ˣ), IsUnit (1 - (u : Rz K ζ)) →
      ιL (tateToricPoint (Rz K ζ) 1 u).2 = (toricPoint (Fz K ζ) 1 (ι u)).2 := fun u hu =>
    coeffMap_frac_toric_snd K u hu
  have hιinv : ι c * ι ((c⁻¹ : (Rz K ζ)ˣ) : Rz K ζ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]

  obtain ⟨hcF, hciF, hinv, -⟩ := ModularCurve.toricPoint_add_toricPoint_of_charZero (Fz K ζ) (ι c)
    (ι ((c⁻¹ : (Rz K ζ)ˣ) : Rz K ζ)) (hne0 c) (hne0 c⁻¹) (hne1 hc1) (hne1 hci1)
  refine ⟨?_, ?_⟩
  ·
    have h : ((tateLaurent (Rz K ζ)).map ιL).toAffine.Equation (ιL (tateToricPoint (Rz K ζ) 1 c).1)
        (ιL (tateToricPoint (Rz K ζ) 1 c).2) := by
      rw [hW, hx c h1c, hy c h1c]; exact hcF.left
    exact (map_equation _ hιLinj _ _).mp h
  ·
    have h : negRel ((tateLaurent (Rz K ζ)).map ιL) (ιL (tateToricPoint (Rz K ζ) 1 c).1)
        (ιL (tateToricPoint (Rz K ζ) 1 c).2) (ιL (tateToricPoint (Rz K ζ) 1 c⁻¹).1)
        (ιL (tateToricPoint (Rz K ζ) 1 c⁻¹).2) := by
      rw [hW, hx c h1c, hy c h1c, hx c⁻¹ h1ci, hy c⁻¹ h1ci]
      exact negRel_of_add_eq_zero (hinv hιinv)
    exact negRel_of_map ιL _ hιLinj h

theorem relations_R_two (c d : (Rz K ζ)ˣ) (h1c : IsUnit (1 - (c : Rz K ζ)))
    (h1d : IsUnit (1 - (d : Rz K ζ))) (h1cd : IsUnit (1 - ((c * d : (Rz K ζ)ˣ) : Rz K ζ)))
    (hc1 : (c : Rz K ζ) ≠ 1) (hd1 : (d : Rz K ζ) ≠ 1) (hcd1 : ((c * d : (Rz K ζ)ˣ) : Rz K ζ) ≠ 1) :
    ((tateToricPoint (Rz K ζ) 1 c).1 ≠ (tateToricPoint (Rz K ζ) 1 d).1 →
      chordRel (tateLaurent (Rz K ζ)) (tateToricPoint (Rz K ζ) 1 c).1 (tateToricPoint (Rz K ζ) 1 c).2
        (tateToricPoint (Rz K ζ) 1 d).1 (tateToricPoint (Rz K ζ) 1 d).2
        (tateToricPoint (Rz K ζ) 1 (c * d)).1 (tateToricPoint (Rz K ζ) 1 (c * d)).2) ∧
    (c = d →
      dblRel (tateLaurent (Rz K ζ)) (tateToricPoint (Rz K ζ) 1 c).1 (tateToricPoint (Rz K ζ) 1 c).2
        (tateToricPoint (Rz K ζ) 1 (c * d)).1 (tateToricPoint (Rz K ζ) 1 (c * d)).2) := by
  classical
  let ι : Rz K ζ →+* Fz K ζ := algebraMap (Rz K ζ) (Fz K ζ)
  let ιL : LaurentSeries (Rz K ζ) →+* LaurentSeries (Fz K ζ) := coeffMap ι
  have hιinj : Function.Injective ι := IsFractionRing.injective (Rz K ζ) (Fz K ζ)
  have hιLinj : Function.Injective ιL := coeffMap_injective ι hιinj
  have hW : (tateLaurent (Rz K ζ)).map ιL = tateLaurent (Fz K ζ) := tateLaurent_map ι
  have hne0 : ∀ u : (Rz K ζ)ˣ, ι u ≠ 0 := fun u => (map_ne_zero_iff ι hιinj).mpr u.ne_zero
  have hne1 : ∀ {u : (Rz K ζ)ˣ}, (u : Rz K ζ) ≠ 1 → ι u ≠ 1 := fun hu h =>
    hu (hιinj (h.trans (map_one ι).symm))
  have hx : ∀ (u : (Rz K ζ)ˣ), IsUnit (1 - (u : Rz K ζ)) →
      ιL (tateToricPoint (Rz K ζ) 1 u).1 = (toricPoint (Fz K ζ) 1 (ι u)).1 := fun u hu =>
    coeffMap_frac_toric_fst K u hu
  have hy : ∀ (u : (Rz K ζ)ˣ), IsUnit (1 - (u : Rz K ζ)) →
      ιL (tateToricPoint (Rz K ζ) 1 u).2 = (toricPoint (Fz K ζ) 1 (ι u)).2 := fun u hu =>
    coeffMap_frac_toric_snd K u hu
  have hιmul : ι c * ι d = ι ((c * d : (Rz K ζ)ˣ) : Rz K ζ) := by rw [Units.val_mul, map_mul]

  obtain ⟨hcF, hdF, -, hmul⟩ := ModularCurve.toricPoint_add_toricPoint_of_charZero (Fz K ζ) (ι c)
    (ι d) (hne0 c) (hne0 d) (hne1 hc1) (hne1 hd1)
  have hcd : ι c * ι d ≠ 1 := by rw [hιmul]; exact hne1 hcd1
  obtain ⟨hcdF, hsum⟩ := hmul hcd
  refine ⟨?_, ?_⟩
  ·
    intro hxne
    have hxneF : (toricPoint (Fz K ζ) 1 (ι c)).1 ≠ (toricPoint (Fz K ζ) 1 (ι d)).1 := by
      rw [← hx c h1c, ← hx d h1d]; exact fun h => hxne (hιLinj h)
    have h : chordRel ((tateLaurent (Rz K ζ)).map ιL) (ιL (tateToricPoint (Rz K ζ) 1 c).1)
        (ιL (tateToricPoint (Rz K ζ) 1 c).2) (ιL (tateToricPoint (Rz K ζ) 1 d).1)
        (ιL (tateToricPoint (Rz K ζ) 1 d).2) (ιL (tateToricPoint (Rz K ζ) 1 (c * d)).1)
        (ιL (tateToricPoint (Rz K ζ) 1 (c * d)).2) := by
      rw [hW, hx c h1c, hy c h1c, hx d h1d, hy d h1d, hx (c * d) h1cd, hy (c * d) h1cd, ← hιmul]
      exact chordRel_of_add_eq hsum hxneF
    exact chordRel_of_map ιL _ hιLinj h
  ·
    intro hcd'
    subst hcd'
    have h : dblRel ((tateLaurent (Rz K ζ)).map ιL) (ιL (tateToricPoint (Rz K ζ) 1 c).1)
        (ιL (tateToricPoint (Rz K ζ) 1 c).2) (ιL (tateToricPoint (Rz K ζ) 1 (c * c)).1)
        (ιL (tateToricPoint (Rz K ζ) 1 (c * c)).2) := by
      rw [hW, hx c h1c, hy c h1c, hx (c * c) h1cd, hy (c * c) h1cd, ← hιmul]
      exact dblRel_of_add_self_eq hsum
    exact dblRel_of_map ιL _ hιLinj h

theorem relations_K_one (hζ0 : ζ ≠ 0) {a : ℕ} (ha : ζ ^ a ≠ 1) :
    (tateLaurent K).toAffine.Equation (toricPoint K 1 (ζ ^ a)).1 (toricPoint K 1 (ζ ^ a)).2 ∧
    negRel (tateLaurent K) (toricPoint K 1 (ζ ^ a)).1 (toricPoint K 1 (ζ ^ a)).2
        (toricPoint K 1 (ζ ^ a)⁻¹).1 (toricPoint K 1 (ζ ^ a)⁻¹).2 := by
  let σL : LaurentSeries (Rz K ζ) →+* LaurentSeries K := coeffMap (spec K ζ)
  have hW : (tateLaurent (Rz K ζ)).map σL = tateLaurent K := tateLaurent_map (spec K ζ)
  obtain ⟨heq, hneg⟩ := relations_R_one K (cX K hζ0 a) (isUnit_one_sub_cX K hζ0 ha)
    (isUnit_one_sub_cX_inv K hζ0 ha) (cX_ne_one K hζ0 ha)
  have hxa : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a)).1 = (toricPoint K 1 (ζ ^ a)).1 :=
    coeffMap_spec_toric_fst K hζ0 ha
  have hya : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a)).2 = (toricPoint K 1 (ζ ^ a)).2 :=
    coeffMap_spec_toric_snd K hζ0 ha
  have hxai : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a)⁻¹).1 = (toricPoint K 1 (ζ ^ a)⁻¹).1 :=
    coeffMap_spec_toric_inv_fst K hζ0 ha
  have hyai : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a)⁻¹).2 = (toricPoint K 1 (ζ ^ a)⁻¹).2 :=
    coeffMap_spec_toric_inv_snd K hζ0 ha
  refine ⟨?_, ?_⟩
  · have h : ((tateLaurent (Rz K ζ)).map σL).toAffine.Equation
        (σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a)).1)
        (σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a)).2) := heq.map σL
    rw [hW, hxa, hya] at h
    exact h
  · have h := negRel_map σL _ hneg
    rw [hW, hxa, hya, hxai, hyai] at h
    exact h

theorem relations_K_two (hζ0 : ζ ≠ 0) {a b : ℕ} (ha : ζ ^ a ≠ 1) (hb : ζ ^ b ≠ 1)
    (hab : ζ ^ (a + b) ≠ 1) :
    ((toricPoint K 1 (ζ ^ a)).1 ≠ (toricPoint K 1 (ζ ^ b)).1 →
      chordRel (tateLaurent K) (toricPoint K 1 (ζ ^ a)).1 (toricPoint K 1 (ζ ^ a)).2
        (toricPoint K 1 (ζ ^ b)).1 (toricPoint K 1 (ζ ^ b)).2
        (toricPoint K 1 (ζ ^ (a + b))).1 (toricPoint K 1 (ζ ^ (a + b))).2) ∧
    (a = b →
      dblRel (tateLaurent K) (toricPoint K 1 (ζ ^ a)).1 (toricPoint K 1 (ζ ^ a)).2
        (toricPoint K 1 (ζ ^ (a + b))).1 (toricPoint K 1 (ζ ^ (a + b))).2) := by
  let σL : LaurentSeries (Rz K ζ) →+* LaurentSeries K := coeffMap (spec K ζ)
  have hW : (tateLaurent (Rz K ζ)).map σL = tateLaurent K := tateLaurent_map (spec K ζ)
  have hcd : cX K hζ0 a * cX K hζ0 b = cX K hζ0 (a + b) := cX_mul K hζ0 a b
  have h1c := isUnit_one_sub_cX K hζ0 ha
  have h1d := isUnit_one_sub_cX K hζ0 hb
  have h1cd : IsUnit (1 - ((cX K hζ0 a * cX K hζ0 b : (Rz K ζ)ˣ) : Rz K ζ)) := by
    rw [hcd]; exact isUnit_one_sub_cX K hζ0 hab
  have hc1 := cX_ne_one K hζ0 ha
  have hd1 := cX_ne_one K hζ0 hb
  have hcd1 : ((cX K hζ0 a * cX K hζ0 b : (Rz K ζ)ˣ) : Rz K ζ) ≠ 1 := by
    rw [hcd]; exact cX_ne_one K hζ0 hab
  obtain ⟨hchord, hdbl⟩ := relations_R_two K (cX K hζ0 a) (cX K hζ0 b) h1c h1d h1cd hc1 hd1 hcd1

  have hxa : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a)).1 = (toricPoint K 1 (ζ ^ a)).1 :=
    coeffMap_spec_toric_fst K hζ0 ha
  have hya : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a)).2 = (toricPoint K 1 (ζ ^ a)).2 :=
    coeffMap_spec_toric_snd K hζ0 ha
  have hxb : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 b)).1 = (toricPoint K 1 (ζ ^ b)).1 :=
    coeffMap_spec_toric_fst K hζ0 hb
  have hyb : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 b)).2 = (toricPoint K 1 (ζ ^ b)).2 :=
    coeffMap_spec_toric_snd K hζ0 hb
  have hxab : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a * cX K hζ0 b)).1
      = (toricPoint K 1 (ζ ^ (a + b))).1 := by
    rw [hcd]; exact coeffMap_spec_toric_fst K hζ0 hab
  have hyab : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a * cX K hζ0 b)).2
      = (toricPoint K 1 (ζ ^ (a + b))).2 := by
    rw [hcd]; exact coeffMap_spec_toric_snd K hζ0 hab
  refine ⟨?_, ?_⟩
  · intro hxne
    have hxneR : (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a)).1
        ≠ (tateToricPoint (Rz K ζ) 1 (cX K hζ0 b)).1 := by
      intro h; apply hxne; rw [← hxa, ← hxb, h]
    have h := chordRel_map σL _ (hchord hxneR)
    rw [hW, hxa, hya, hxb, hyb, hxab, hyab] at h
    exact h
  · intro habeq
    subst habeq
    have h := dblRel_map σL _ (hdbl rfl)
    rw [hW, hxa, hya, hxab, hyab] at h
    exact h

theorem coeff_zero_toricPoint_fst (a : K) :
    (toricPoint K 1 a).1.coeff 0 = a / (1 - a) ^ 2 := by
  rw [toricPoint_fst]
  change ((PowerSeries.mk _ : PowerSeries K) : LaurentSeries K).coeff 0 = _
  rw [PowerSeries.coeff_coe, if_neg (lt_irrefl 0), Int.natAbs_zero, PowerSeries.coeff_mk, if_pos rfl]

theorem coeff_zero_toricPoint_snd (a : K) :
    (toricPoint K 1 a).2.coeff 0 = a ^ 2 / (1 - a) ^ 3 := by
  rw [toricPoint_snd]
  change ((PowerSeries.mk _ : PowerSeries K) : LaurentSeries K).coeff 0 = _
  rw [PowerSeries.coeff_coe, if_neg (lt_irrefl 0), Int.natAbs_zero, PowerSeries.coeff_mk, if_pos rfl]

theorem toricPoint_fst_ne {a b : K} (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hab1 : a * b ≠ 1) :
    (toricPoint K 1 a).1 ≠ (toricPoint K 1 b).1 := by
  intro h
  have h0 := congrArg (fun s : LaurentSeries K => s.coeff 0) h
  simp only [coeff_zero_toricPoint_fst] at h0
  have h1a : (1 - a) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm ha1))
  have h1b : (1 - b) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hb1))
  rw [div_eq_div_iff h1a h1b] at h0
  have key : (a - b) * (1 - a * b) = 0 := by linear_combination h0
  rcases mul_eq_zero.mp key with h2 | h2
  · exact hab (sub_eq_zero.mp h2)
  · exact hab1 (sub_eq_zero.mp h2).symm

theorem two_mul_snd_add_fst_ne_zero {a : K} (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : a ^ 2 ≠ 1) :
    2 * (toricPoint K 1 a).2 + (toricPoint K 1 a).1 ≠ 0 := by
  intro h
  have h0 := congrArg (fun s : LaurentSeries K => s.coeff 0) h
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero] at h0
  rw [show ((2 : LaurentSeries K) * (toricPoint K 1 a).2).coeff 0 = 2 * (toricPoint K 1 a).2.coeff 0 by
    rw [show (2 : LaurentSeries K) = HahnSeries.C (2 : K) by rw [map_ofNat], HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, smul_eq_mul]] at h0
  rw [coeff_zero_toricPoint_fst, coeff_zero_toricPoint_snd] at h0
  have h1 : (1 - a) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  rw [mul_div_assoc', div_add_div _ _ (pow_ne_zero 3 h1) (pow_ne_zero 2 h1), div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · have key : (1 - a) ^ 2 * (a * (1 + a)) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp key with h2 | h2
    · exact pow_ne_zero 2 h1 h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact ha0 h3
      · apply ha2
        have : a = -1 := by linear_combination h3
        rw [this]; norm_num
  · exact mul_ne_zero (pow_ne_zero 3 h1) (pow_ne_zero 2 h1) h0

theorem tateLaurent_a₁ : (tateLaurent K).a₁ = 1 := by
  simp [tateLaurent, tatePowerSeries]

theorem tateLaurent_a₃ : (tateLaurent K).a₃ = 0 := by
  simp [tateLaurent, tatePowerSeries]

end Toric

section Assembly

variable (K : Type u) [Field K] (M : ℕ) (ζ : K)
  (L : Type v) [Field L] [DecidableEq L] [Algebra (LaurentSeries K) L]

theorem main (hM : 2 ≤ M) (hζ : IsPrimitiveRoot ζ M) :
    ∃ P : ((tateLaurent K).baseChange L).toAffine.Point,
      (∀ n : ℕ, n • P = 0 ↔ M ∣ n) ∧
      ∀ n : ℕ, ¬ M ∣ n →
        ∃ h : ((tateLaurent K).baseChange L).toAffine.Nonsingular
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).1)
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).2),
          n • P = WeierstrassCurve.Affine.Point.some
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).1)
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).2) h := by

  set θ : LaurentSeries K →+* L := algebraMap (LaurentSeries K) L with hθ
  have hθinj : Function.Injective θ := θ.injective
  haveI : ((tateLaurent K).baseChange L).IsElliptic :=
    inferInstanceAs (((tateLaurent K).map θ).IsElliptic)

  have hM0 : M ≠ 0 := by omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hM0
  have hpow : ∀ {n : ℕ}, ζ ^ n ≠ 1 ↔ ¬ M ∣ n := fun {n} => (hζ.pow_eq_one_iff_dvd n).not
  have h1 : ¬ M ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
  have hζ1 : ζ ^ 1 ≠ 1 := hpow.mpr h1

  have hns : ∀ {n : ℕ}, ¬ M ∣ n → ((tateLaurent K).baseChange L).toAffine.Nonsingular
      (θ (toricPoint K 1 (ζ ^ n)).1) (θ (toricPoint K 1 (ζ ^ n)).2) := by
    intro n hn
    obtain ⟨heq, -⟩ := relations_K_one K hζ0 (hpow.mpr hn)
    exact equation_iff_nonsingular.mp (heq.map θ)

  have hneg : ∀ {n : ℕ}, ¬ M ∣ n → negRel ((tateLaurent K).baseChange L)
      (θ (toricPoint K 1 (ζ ^ n)).1) (θ (toricPoint K 1 (ζ ^ n)).2)
      (θ (toricPoint K 1 (ζ ^ n)⁻¹).1) (θ (toricPoint K 1 (ζ ^ n)⁻¹).2) := by
    intro n hn
    obtain ⟨-, h⟩ := relations_K_one K hζ0 (hpow.mpr hn)
    exact negRel_map θ (tateLaurent K) h

  have hchord : ∀ {n : ℕ} (hn : ¬ M ∣ n) (hn1 : ¬ M ∣ n + 1), ζ ^ n ≠ ζ ^ 1 →
      (Point.some _ _ (hns hn) : ((tateLaurent K).baseChange L).toAffine.Point) + Point.some _ _ (hns h1)
        = Point.some _ _ (hns hn1) := by
    intro n hn hn1 hne
    have hab : ζ ^ (n + 1) ≠ 1 := hpow.mpr hn1
    have hxne : (toricPoint K 1 (ζ ^ n)).1 ≠ (toricPoint K 1 (ζ ^ 1)).1 :=
      toricPoint_fst_ne K (hpow.mpr hn) hζ1 hne (by rw [← pow_add]; exact hab)
    obtain ⟨hc, -⟩ := relations_K_two K hζ0 (hpow.mpr hn) hζ1 hab
    have h := chordRel_map θ (tateLaurent K) (hc hxne)
    exact add_eq_of_chordRel h (fun h' => hxne (hθinj h')) _ _ _

  have hdbl : ∀ (h2 : ¬ M ∣ 1 + 1),
      (Point.some _ _ (hns h1) : ((tateLaurent K).baseChange L).toAffine.Point) + Point.some _ _ (hns h1)
        = Point.some _ _ (hns h2) := by
    intro h2
    obtain ⟨-, hd⟩ := relations_K_two K hζ0 hζ1 hζ1 (hpow.mpr h2)
    have h := dblRel_map θ (tateLaurent K) (hd rfl)
    refine add_eq_of_dblRel h ?_ _ _
    intro hy
    have hsq : (ζ ^ 1) ^ 2 ≠ 1 := by rw [← pow_mul]; exact hpow.mpr h2
    apply two_mul_snd_add_fst_ne_zero K (pow_ne_zero 1 hζ0) hζ1 hsq
    apply hθinj
    simp only [negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, tateLaurent_a₁,
      tateLaurent_a₃, map_one, map_zero, one_mul, sub_zero] at hy
    rw [map_add, map_mul, map_ofNat, map_zero]
    linear_combination hy

  set P : ((tateLaurent K).baseChange L).toAffine.Point := Point.some _ _ (hns h1) with hPdef
  have ladder : ∀ n : ℕ, (M ∣ n → n • P = 0) ∧
      (∀ hn : ¬ M ∣ n, n • P = Point.some _ _ (hns hn)) := by
    intro n
    induction n with
    | zero => exact ⟨fun _ => zero_nsmul _, fun hn => (hn (dvd_zero M)).elim⟩
    | succ n ih =>
      obtain ⟨ih0, ih1⟩ := ih
      rw [succ_nsmul]
      by_cases hn : M ∣ n
      · rw [ih0 hn, zero_add]
        have hn1 : ¬ M ∣ n + 1 := fun h => h1 ((Nat.dvd_add_right hn).mp h)
        refine ⟨fun h => (hn1 h).elim, fun _ => ?_⟩
        have he : ζ ^ 1 = ζ ^ (n + 1) := by
          rw [pow_one, pow_succ, (hζ.pow_eq_one_iff_dvd n).mpr hn, one_mul]
        exact point_some_congr (by rw [he]) (by rw [he]) _ _
      · rw [ih1 hn]
        by_cases hn1 : M ∣ n + 1
        · refine ⟨fun _ => ?_, fun h => (h hn1).elim⟩
          have he : ζ ^ n = (ζ ^ 1)⁻¹ :=
            eq_inv_of_mul_eq_one_left (by
              rw [pow_one, ← pow_succ]; exact (hζ.pow_eq_one_iff_dvd _).mpr hn1)
          obtain ⟨hx, hy⟩ := hneg h1
          apply Point.add_of_Y_eq
          · rw [he]; exact hx
          · rw [he]; exact hy
        · refine ⟨fun h => (hn1 h).elim, fun _ => ?_⟩
          by_cases he : ζ ^ n = ζ ^ 1
          ·
            have he2 : ζ ^ (n + 1) = ζ ^ (1 + 1) := by rw [pow_succ, he, ← pow_succ]
            have h2 : ¬ M ∣ 1 + 1 := by
              intro h
              apply hn1
              have h3 : ζ ^ (n + 1) = 1 := by rw [he2]; exact (hζ.pow_eq_one_iff_dvd _).mpr h
              exact (hζ.pow_eq_one_iff_dvd _).mp h3
            calc (Point.some _ _ (hns hn) : ((tateLaurent K).baseChange L).toAffine.Point) + P
                = P + P := by
                  rw [hPdef]
                  exact congrArg (· + _) (point_some_congr (by rw [he]) (by rw [he]) _ _)
              _ = Point.some _ _ (hns h2) := hdbl h2
              _ = Point.some _ _ (hns hn1) := point_some_congr (by rw [he2]) (by rw [he2]) _ _
          ·
            exact hchord hn hn1 he
  refine ⟨P, fun n => ⟨fun h => ?_, (ladder n).1⟩, fun n hn => ⟨hns hn, (ladder n).2 hn⟩⟩
  by_contra hn
  rw [(ladder n).2 hn] at h
  exact Point.some_ne_zero _ h

end Assembly

end P2MToricLevel
p2m_reactivate "P2MW.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot.ModularCurve.P2MToricLevel"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot.ModularCurve.P2MToricLevel P2MW.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot.ModularCurve.P2MToricLevel P2MW.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot.ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot.ModularCurve WeierstrassCurve WeierstrassCurve.Affine"

universe u v in
theorem solution
    (K : Type u) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K) (hζ : IsPrimitiveRoot ζ M)
    (L : Type v) [Field L] [DecidableEq L] [Algebra (LaurentSeries K) L] :
    ∃ P : ((tateLaurent K).baseChange L).toAffine.Point,
      (∀ n : ℕ, n • P = 0 ↔ M ∣ n) ∧
      ∀ n : ℕ, ¬ M ∣ n →
        ∃ h : ((tateLaurent K).baseChange L).toAffine.Nonsingular
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).1)
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).2),
          n • P = WeierstrassCurve.Affine.Point.some
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).1)
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).2) h :=
  ModularCurve.P2MToricLevel.main K M ζ L hM hζ

end S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
end P2MW
export P2MW.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot (solution)

-- Prove2me | solution 1 for ModularCurve.exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/7d64bafb-558e-5d88-82b2-6f9cc98957f9

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_toricPoint_add_nonToricPoint_of_charZero
import Theorems.Thm_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one
import Theorems.Thm_ModularCurve_equation_tateBase_nonToricPoint
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivY
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false

noncomputable section

p2m_open "Polynomial WeierstrassCurve~Coeff WeierstrassCurve.Affine"

namespace ModularCurve
p2m_export "ModularCurve" "tateUnivX tateUnivY slotSubst nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd toricPoint toricPoint_fst toricPoint_snd tatePowerSeries laurentOfInt laurentOfInt_apply tateLaurent qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_injective qTwist_qExpand coeffMap coeffMap_coeff tateToricPoint tateToricPoint_fst tateToricPoint_snd tateToricPoint_eq_toricPoint tateBase_map_qTwist toricPoint_add_nonToricPoint_of_charZero qTwist_nonToricPoint_of_pow_eq_one equation_tateBase_nonToricPoint coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
p2m_open "ModularCurve"

namespace P2MTateInertia

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

theorem coeffMap_qExpand (p : ℕ) [NeZero p] (x : LaurentSeries R) :
    coeffMap f (qExpand R p x) = qExpand S p (coeffMap f x) := by
  ext k
  by_cases hk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd p _ hk, qExpand_coeff_of_not_dvd p _ hk, map_zero]

theorem tateBase_map (p : ℕ) [NeZero p] : (tateBase R p).map (coeffMap f) = tateBase S p := by
  have h : (coeffMap f).comp (qExpand R p) = (qExpand S p).comp (coeffMap f) :=
    RingHom.ext fun x => coeffMap_qExpand f p x
  rw [tateBase, tateBase, WeierstrassCurve.map_map, h, ← WeierstrassCurve.map_map, tateLaurent_map]

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

theorem coeffMap_nonToricPoint_fst (p : ℕ) (c : Rˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    coeffMap f (nonToricPoint R p c j).1 = (nonToricPoint S p (Units.map (f : R →* S) c) j).1 := by
  rw [nonToricPoint_fst, nonToricPoint_fst, coeffMap_ofPowerSeries]
  congr 1
  ext n
  rw [PowerSeries.coeff_map, coeff_slotSubst_tateUnivX p c j hj hjp n,
    coeff_slotSubst_tateUnivX p (Units.map (f : R →* S) c) j hj hjp n]
  simp only [map_sub, map_sum, map_mul, map_add, map_pow, map_natCast, apply_ite f, map_zero,
    map_ofNat, Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

theorem coeffMap_nonToricPoint_snd (p : ℕ) (c : Rˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    coeffMap f (nonToricPoint R p c j).2 = (nonToricPoint S p (Units.map (f : R →* S) c) j).2 := by
  rw [nonToricPoint_snd, nonToricPoint_snd, coeffMap_ofPowerSeries]
  congr 1
  ext n
  rw [PowerSeries.coeff_map, coeff_slotSubst_tateUnivY p c j hj hjp n,
    coeff_slotSubst_tateUnivY p (Units.map (f : R →* S) c) j hj hjp n]
  simp only [map_sub, map_sum, map_mul, map_add, map_pow, map_natCast, apply_ite f, map_zero,
    Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

end Transport

section Coeff

theorem coeff_zero_toricPoint_fst (K : Type*) [Field K] (p : ℕ) (a : K) :
    (toricPoint K p a).1.coeff 0 = a / (1 - a) ^ 2 := by
  rw [toricPoint_fst]
  change ((PowerSeries.mk _ : PowerSeries K) : LaurentSeries K).coeff 0 = _
  rw [PowerSeries.coeff_coe, if_neg (lt_irrefl 0), Int.natAbs_zero, PowerSeries.coeff_mk, if_pos rfl]

theorem coeff_toricPoint_of_not_dvd (K : Type*) [Field K] (p : ℕ) (a : K) {k : ℤ}
    (hk : ¬ (p : ℤ) ∣ k) :
    (toricPoint K p a).1.coeff k = 0 ∧ (toricPoint K p a).2.coeff k = 0 := by
  rw [toricPoint_fst, toricPoint_snd]
  change ((PowerSeries.mk _ : PowerSeries K) : LaurentSeries K).coeff k = 0 ∧
    ((PowerSeries.mk _ : PowerSeries K) : LaurentSeries K).coeff k = 0
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  by_cases hk0 : k < 0
  · rw [if_pos hk0, if_pos hk0]; exact ⟨rfl, rfl⟩
  · rw [if_neg hk0, if_neg hk0, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    have hkabs : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg (not_lt.mp hk0)
    have hm0 : k.natAbs ≠ 0 := by
      intro h; apply hk; rw [← hkabs, h]; exact dvd_zero _
    have hpm : ¬ p ∣ k.natAbs := by
      intro h; apply hk; rw [← hkabs]; exact Int.natCast_dvd_natCast.mpr h
    have hsum : ∀ (g : ℕ → K),
        (∑ d ∈ k.natAbs.divisors, if p ∣ d then g d else 0) = 0 := by
      intro g
      refine Finset.sum_eq_zero fun d hd => ?_
      rw [if_neg]
      intro hpd
      exact hpm (dvd_trans hpd (Nat.dvd_of_mem_divisors hd))
    rw [if_neg hm0, if_neg hm0, hsum, hsum]
    simp [hpm]

variable {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ)

theorem coeff_zero_nonToricPoint_fst (hj : 0 < j) (hjp : j < p) :
    (nonToricPoint K p c j).1.coeff 0 = 0 := by
  rw [nonToricPoint_fst]
  change ((slotSubst K p c j tateUnivX : PowerSeries K) : LaurentSeries K).coeff 0 = 0
  rw [PowerSeries.coeff_coe, if_neg (lt_irrefl 0), Int.natAbs_zero,
    coeff_slotSubst_tateUnivX p c j hj hjp 0]
  simp

theorem coeff_one_nonToricPoint_fst (hj : 0 < j) (hjp : j < p) :
    (nonToricPoint K p c j).1.coeff 1 =
      (if j = 1 then (c : K) else 0) + (if j + 1 = p then ((c⁻¹ : Kˣ) : K) else 0) := by
  rw [nonToricPoint_fst]
  change ((slotSubst K p c j tateUnivX : PowerSeries K) : LaurentSeries K).coeff 1 = _
  rw [PowerSeries.coeff_coe, if_neg (by norm_num), show (1 : ℤ).natAbs = 1 from rfl,
    coeff_slotSubst_tateUnivX p c j hj hjp 1]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, Nat.divisors_zero,
    Finset.sum_empty, Nat.divisors_one, Finset.sum_singleton, zero_add]
  have h1 : ¬ (1 = p * 1 + j * 1) := by omega
  have h2 : ¬ (1 = p * 1) := by omega
  rw [if_neg h1, if_neg h2]
  by_cases hj1 : j = 1
  · subst hj1
    by_cases hp : 1 + 1 = p
    · rw [if_pos (dvd_refl 1), if_pos (by omega : 1 + 1 * 1 = p * 1), if_pos rfl, if_pos hp]
      simp
    · rw [if_pos (dvd_refl 1), if_neg (by omega : ¬ 1 + 1 * 1 = p * 1), if_pos rfl, if_neg hp]
      simp
  · have hnd : ¬ j ∣ 1 := fun h => hj1 (Nat.dvd_one.mp h)
    by_cases hp : j + 1 = p
    · rw [if_neg hnd, if_pos (by omega : 1 + j * 1 = p * 1), if_neg hj1, if_pos hp]
      simp
    · rw [if_neg hnd, if_neg (by omega : ¬ 1 + j * 1 = p * 1), if_neg hj1, if_neg hp]
      simp

theorem coeff_one_nonToricPoint_snd (hj : 0 < j) (hjp : j < p) :
    (nonToricPoint K p c j).2.coeff 1 = -(if j + 1 = p then ((c⁻¹ : Kˣ) : K) else 0) := by
  rw [nonToricPoint_snd]
  change ((slotSubst K p c j tateUnivY : PowerSeries K) : LaurentSeries K).coeff 1 = _
  rw [PowerSeries.coeff_coe, if_neg (by norm_num), show (1 : ℤ).natAbs = 1 from rfl,
    coeff_slotSubst_tateUnivY p c j hj hjp 1]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, Nat.divisors_zero,
    Finset.sum_empty, Nat.divisors_one, Finset.sum_singleton, zero_add]
  have h1 : ¬ (1 = p * 1 + j * 1) := by omega
  have h2 : ¬ (1 = p * 1) := by omega
  rw [if_neg h1, if_neg h2]
  have hhead : (if j ∣ 1 then (((1 / j).choose 2 : ℕ) : K) * (c : K) ^ (1 / j) else 0) = 0 := by
    split_ifs with h
    · have hj1 : j = 1 := Nat.dvd_one.mp h
      subst hj1
      simp
    · rfl
  rw [hhead]
  by_cases hp : j + 1 = p
  · rw [if_pos (by omega : 1 + j * 1 = p * 1), if_pos hp]
    simp
  · rw [if_neg (by omega : ¬ 1 + j * 1 = p * 1), if_neg hp]
    simp

end Coeff

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

section MapPt

variable {R : Type u} {S : Type v} [Field R] [Field S] [DecidableEq R] [DecidableEq S]

def mapPtFun (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve S) (f : R →+* S)
    (hf : Function.Injective f) (hW : W₀.map f = W₁) :
    W₀.toAffine.Point → W₁.toAffine.Point
  | 0 => 0
  | .some x y h => .some (f x) (f y) (hW ▸ (Affine.map_nonsingular _ hf x y).mpr h)

theorem mapPtFun_add (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve S) (f : R →+* S)
    (hf : Function.Injective f) (hW : W₀.map f = W₁) (P Q : W₀.toAffine.Point) :
    mapPtFun W₀ W₁ f hf hW (P + Q) = mapPtFun W₀ W₁ f hf hW P + mapPtFun W₀ W₁ f hf hW Q := by
  subst hW
  rcases P with (_ | ⟨x₁, y₁, h₁⟩) <;> rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W₀.toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.left hxy.right]
    show (0 : (W₀.map f).toAffine.Point) = .some (f x₁) (f y₁) _ + .some (f x₂) (f y₂) _
    rw [Point.add_of_Y_eq (congr_arg _ hxy.left) (by rw [hxy.right, Affine.map_negY])]
  · have hxy' : ¬((f x₁) = (f x₂) ∧ f y₁ = (W₀.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨h1, h2⟩
      exact hxy ⟨hf h1, hf (by rw [Affine.map_negY] at h2; exact h2)⟩
    rw [Point.add_some hxy]
    show Point.some (f _) (f _) _ = .some (f x₁) (f y₁) _ + .some (f x₂) (f y₂) _
    simp only [Point.add_some hxy', Affine.map_slope, Affine.map_addX, Affine.map_addY]

def mapPt (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve S) (f : R →+* S)
    (hf : Function.Injective f) (hW : W₀.map f = W₁) :
    W₀.toAffine.Point →+ W₁.toAffine.Point where
  toFun := mapPtFun W₀ W₁ f hf hW
  map_zero' := rfl
  map_add' := mapPtFun_add W₀ W₁ f hf hW

theorem mapPt_some (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve S) (f : R →+* S)
    (hf : Function.Injective f) (hW : W₀.map f = W₁) (x y : R) (h : W₀.toAffine.Nonsingular x y)
    (h' : W₁.toAffine.Nonsingular (f x) (f y)) :
    mapPt W₀ W₁ f hf hW (.some x y h) = .some (f x) (f y) h' := rfl

end MapPt

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

def cX (hζ0 : ζ ≠ 0) : (Rz K ζ)ˣ :=
  unitOf K ζ X (by
    show Polynomial.eval₂ (Int.castRingHom K) ζ X ≠ 0
    rw [eval₂_X]; exact hζ0)

theorem val_cX (hζ0 : ζ ≠ 0) : ((cX K hζ0 : (Rz K ζ)ˣ) : Rz K ζ) = algebraMap ℤ[X] (Rz K ζ) X := by
  rw [cX, val_unitOf]

theorem spec_cX (hζ0 : ζ ≠ 0) : spec K ζ (cX K hζ0 : (Rz K ζ)ˣ) = ζ := by
  rw [cX, spec_unitOf]
  show Polynomial.eval₂ (Int.castRingHom K) ζ X = ζ
  rw [eval₂_X]

theorem isUnit_one_sub_cX (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) :
    IsUnit (1 - ((cX K hζ0 : (Rz K ζ)ˣ) : Rz K ζ)) := by
  have h : (1 : Rz K ζ) - ((cX K hζ0 : (Rz K ζ)ˣ) : Rz K ζ) = algebraMap ℤ[X] (Rz K ζ) (1 - X) := by
    rw [val_cX, map_sub, map_one]
  rw [h]
  refine isUnit_algebraMap K ζ ?_
  show Polynomial.eval₂ (Int.castRingHom K) ζ (1 - X) ≠ 0
  rw [eval₂_sub, eval₂_one, eval₂_X]
  exact fun h0 => hζ1 (sub_eq_zero.mp h0).symm

theorem cX_ne_one (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) : ((cX K hζ0 : (Rz K ζ)ˣ) : Rz K ζ) ≠ 1 := by
  intro h
  apply hζ1
  rw [← spec_cX K hζ0, h, map_one]

end Ring

section Descent

variable (K : Type u) [Field K] {ζ : K} (M : ℕ) [NeZero M]

theorem coeffMap_nonToricPoint_one {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {j : ℕ}
    (hj : 0 < j) (hjM : j < M) :
    coeffMap f (nonToricPoint R M 1 j).1 = (nonToricPoint S M 1 j).1 ∧
    coeffMap f (nonToricPoint R M 1 j).2 = (nonToricPoint S M 1 j).2 := by
  have h1 : Units.map (f : R →* S) 1 = 1 := map_one _
  exact ⟨by rw [coeffMap_nonToricPoint_fst f M 1 j hj hjM, h1],
    by rw [coeffMap_nonToricPoint_snd f M 1 j hj hjM, h1]⟩

theorem relations_R_toric (hM : 2 ≤ M) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) :
    (tateBase (Rz K ζ) M).toAffine.Equation (tateToricPoint (Rz K ζ) M (cX K hζ0)).1
        (tateToricPoint (Rz K ζ) M (cX K hζ0)).2 ∧
    chordRel (tateBase (Rz K ζ) M)
        (tateToricPoint (Rz K ζ) M (cX K hζ0)).1 (tateToricPoint (Rz K ζ) M (cX K hζ0)).2
        (nonToricPoint (Rz K ζ) M 1 1).1 (nonToricPoint (Rz K ζ) M 1 1).2
        (nonToricPoint (Rz K ζ) M (cX K hζ0 * 1) 1).1 (nonToricPoint (Rz K ζ) M (cX K hζ0 * 1) 1).2 := by
  classical
  let ι : Rz K ζ →+* Fz K ζ := algebraMap (Rz K ζ) (Fz K ζ)
  let ιL : LaurentSeries (Rz K ζ) →+* LaurentSeries (Fz K ζ) := coeffMap ι
  have hιinj : Function.Injective ι := IsFractionRing.injective (Rz K ζ) (Fz K ζ)
  have hιLinj : Function.Injective ιL := coeffMap_injective ι hιinj
  have hW : (tateBase (Rz K ζ) M).map ιL = tateBase (Fz K ζ) M := tateBase_map ι M
  set c : (Rz K ζ)ˣ := cX K hζ0 with hcdef
  set c' : (Fz K ζ)ˣ := Units.map (ι : Rz K ζ →* Fz K ζ) c with hc'def
  have h1c : IsUnit (1 - (c : Rz K ζ)) := isUnit_one_sub_cX K hζ0 hζ1
  have hc1 : (c : Rz K ζ) ≠ 1 := cX_ne_one K hζ0 hζ1
  have hc'1 : (c' : Fz K ζ) ≠ 1 := by
    intro h; apply hc1
    rw [hc'def, Units.coe_map, MonoidHom.coe_coe] at h
    exact hιinj (h.trans (map_one ι).symm)
  have h1M : 1 < M := by omega

  have hxA : ιL (tateToricPoint (Rz K ζ) M c).1 = (toricPoint (Fz K ζ) M (c' : Fz K ζ)).1 := by
    rw [coeffMap_tateToricPoint_fst ι M c h1c, tateToricPoint_eq_toricPoint]
  have hyA : ιL (tateToricPoint (Rz K ζ) M c).2 = (toricPoint (Fz K ζ) M (c' : Fz K ζ)).2 := by
    rw [coeffMap_tateToricPoint_snd ι M c h1c, tateToricPoint_eq_toricPoint]
  have hxN : ∀ u : (Rz K ζ)ˣ, ιL (nonToricPoint (Rz K ζ) M u 1).1
      = (nonToricPoint (Fz K ζ) M (Units.map (ι : Rz K ζ →* Fz K ζ) u) 1).1 := fun u =>
    coeffMap_nonToricPoint_fst ι M u 1 one_pos h1M
  have hyN : ∀ u : (Rz K ζ)ˣ, ιL (nonToricPoint (Rz K ζ) M u 1).2
      = (nonToricPoint (Fz K ζ) M (Units.map (ι : Rz K ζ →* Fz K ζ) u) 1).2 := fun u =>
    coeffMap_nonToricPoint_snd ι M u 1 one_pos h1M
  have hmap1 : Units.map (ι : Rz K ζ →* Fz K ζ) 1 = 1 := map_one _
  have hmapc : Units.map (ι : Rz K ζ →* Fz K ζ) (c * 1) = c' * 1 := by rw [map_mul, hmap1]

  obtain ⟨hAF, hBF, hCF, hsum⟩ :=
    (ModularCurve.toricPoint_add_nonToricPoint_of_charZero (Fz K ζ) M).1 c' 1 1 hc'1 one_pos h1M
  refine ⟨?_, ?_⟩
  ·
    have h : ((tateBase (Rz K ζ) M).map ιL).toAffine.Equation (ιL (tateToricPoint (Rz K ζ) M c).1)
        (ιL (tateToricPoint (Rz K ζ) M c).2) := by
      rw [hW, hxA, hyA]; exact hAF.left
    exact (map_equation _ hιLinj _ _).mp h
  ·
    have hc'0 : (c' : Fz K ζ) ≠ 0 := c'.ne_zero
    have hxneF : (toricPoint (Fz K ζ) M (c' : Fz K ζ)).1 ≠ (nonToricPoint (Fz K ζ) M 1 1).1 := by
      intro h
      have h0 := congrArg (fun s : LaurentSeries (Fz K ζ) => s.coeff 0) h
      simp only [coeff_zero_toricPoint_fst, coeff_zero_nonToricPoint_fst M 1 1 one_pos h1M] at h0
      have h1 : (1 - (c' : Fz K ζ)) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hc'1))
      exact hc'0 ((div_eq_zero_iff.mp h0).resolve_right h1)
    have h : chordRel ((tateBase (Rz K ζ) M).map ιL) (ιL (tateToricPoint (Rz K ζ) M c).1)
        (ιL (tateToricPoint (Rz K ζ) M c).2) (ιL (nonToricPoint (Rz K ζ) M 1 1).1)
        (ιL (nonToricPoint (Rz K ζ) M 1 1).2) (ιL (nonToricPoint (Rz K ζ) M (c * 1) 1).1)
        (ιL (nonToricPoint (Rz K ζ) M (c * 1) 1).2) := by
      rw [hW, hxA, hyA, hxN, hyN, hxN, hyN, hmap1, hmapc]
      exact chordRel_of_add_eq hsum hxneF
    exact chordRel_of_map ιL _ hιLinj h

theorem relations_R_line {k : ℕ} (hk : 1 ≤ k) (hkM : 1 + k < M) :
    (2 ≤ k → chordRel (tateBase (Rz K ζ) M)
        (nonToricPoint (Rz K ζ) M 1 1).1 (nonToricPoint (Rz K ζ) M 1 1).2
        (nonToricPoint (Rz K ζ) M 1 k).1 (nonToricPoint (Rz K ζ) M 1 k).2
        (nonToricPoint (Rz K ζ) M 1 (1 + k)).1 (nonToricPoint (Rz K ζ) M 1 (1 + k)).2) ∧
    (k = 1 → dblRel (tateBase (Rz K ζ) M)
        (nonToricPoint (Rz K ζ) M 1 1).1 (nonToricPoint (Rz K ζ) M 1 1).2
        (nonToricPoint (Rz K ζ) M 1 (1 + k)).1 (nonToricPoint (Rz K ζ) M 1 (1 + k)).2) := by
  classical
  let ι : Rz K ζ →+* Fz K ζ := algebraMap (Rz K ζ) (Fz K ζ)
  let ιL : LaurentSeries (Rz K ζ) →+* LaurentSeries (Fz K ζ) := coeffMap ι
  have hιinj : Function.Injective ι := IsFractionRing.injective (Rz K ζ) (Fz K ζ)
  have hιLinj : Function.Injective ιL := coeffMap_injective ι hιinj
  have hW : (tateBase (Rz K ζ) M).map ιL = tateBase (Fz K ζ) M := tateBase_map ι M
  have hxN : ∀ {j : ℕ}, 0 < j → j < M → ιL (nonToricPoint (Rz K ζ) M 1 j).1
      = (nonToricPoint (Fz K ζ) M 1 j).1 := fun {j} hj hjM => (coeffMap_nonToricPoint_one M ι hj hjM).1
  have hyN : ∀ {j : ℕ}, 0 < j → j < M → ιL (nonToricPoint (Rz K ζ) M 1 j).2
      = (nonToricPoint (Fz K ζ) M 1 j).2 := fun {j} hj hjM => (coeffMap_nonToricPoint_one M ι hj hjM).2
  have h1M : 1 < M := by omega
  have hkM' : k < M := by omega

  obtain ⟨hBF, hBkF, hCF, hsum⟩ :=
    (ModularCurve.toricPoint_add_nonToricPoint_of_charZero (Fz K ζ) M).2.1 1 1 1 k one_pos
      (by omega) hkM
  rw [show ((1 : (Fz K ζ)ˣ) * 1) = 1 from mul_one 1] at hCF
  have hsum' : (Point.some (nonToricPoint (Fz K ζ) M 1 1).1 (nonToricPoint (Fz K ζ) M 1 1).2 hBF :
      (tateBase (Fz K ζ) M).toAffine.Point)
      + Point.some (nonToricPoint (Fz K ζ) M 1 k).1 (nonToricPoint (Fz K ζ) M 1 k).2 hBkF
      = Point.some (nonToricPoint (Fz K ζ) M 1 (1 + k)).1 (nonToricPoint (Fz K ζ) M 1 (1 + k)).2
        hCF := by
    rw [hsum]; exact point_some_congr (by rw [mul_one]) (by rw [mul_one]) _ _
  refine ⟨fun hk2 => ?_, fun hk1 => ?_⟩
  ·
    have hxneF : (nonToricPoint (Fz K ζ) M 1 1).1 ≠ (nonToricPoint (Fz K ζ) M 1 k).1 := by
      intro h
      have h0 := congrArg (fun s : LaurentSeries (Fz K ζ) => s.coeff 1) h
      simp only [coeff_one_nonToricPoint_fst M 1 1 one_pos h1M,
        coeff_one_nonToricPoint_fst M 1 k (by omega) hkM', if_neg (show ¬ 1 + 1 = M by omega),
        if_neg (show ¬ k = 1 by omega), if_neg (show ¬ k + 1 = M by omega), add_zero,
        Units.val_one] at h0
      exact one_ne_zero h0
    have h : chordRel ((tateBase (Rz K ζ) M).map ιL) (ιL (nonToricPoint (Rz K ζ) M 1 1).1)
        (ιL (nonToricPoint (Rz K ζ) M 1 1).2) (ιL (nonToricPoint (Rz K ζ) M 1 k).1)
        (ιL (nonToricPoint (Rz K ζ) M 1 k).2) (ιL (nonToricPoint (Rz K ζ) M 1 (1 + k)).1)
        (ιL (nonToricPoint (Rz K ζ) M 1 (1 + k)).2) := by
      rw [hW, hxN one_pos h1M, hyN one_pos h1M, hxN (by omega) hkM', hyN (by omega) hkM',
        hxN (by omega) hkM, hyN (by omega) hkM]
      exact chordRel_of_add_eq hsum' hxneF
    exact chordRel_of_map ιL _ hιLinj h
  ·
    subst hk1
    have hsum'' : (Point.some (nonToricPoint (Fz K ζ) M 1 1).1 (nonToricPoint (Fz K ζ) M 1 1).2 hBF :
        (tateBase (Fz K ζ) M).toAffine.Point)
        + Point.some (nonToricPoint (Fz K ζ) M 1 1).1 (nonToricPoint (Fz K ζ) M 1 1).2 hBF
        = Point.some (nonToricPoint (Fz K ζ) M 1 (1 + 1)).1 (nonToricPoint (Fz K ζ) M 1 (1 + 1)).2
          hCF := hsum'
    have h : dblRel ((tateBase (Rz K ζ) M).map ιL) (ιL (nonToricPoint (Rz K ζ) M 1 1).1)
        (ιL (nonToricPoint (Rz K ζ) M 1 1).2) (ιL (nonToricPoint (Rz K ζ) M 1 (1 + 1)).1)
        (ιL (nonToricPoint (Rz K ζ) M 1 (1 + 1)).2) := by
      rw [hW, hxN one_pos h1M, hyN one_pos h1M, hxN (by omega) hkM, hyN (by omega) hkM]
      exact dblRel_of_add_self_eq hsum''
    exact dblRel_of_map ιL _ hιLinj h

theorem relations_R_inv (hM : 2 ≤ M) :
    negRel (tateBase (Rz K ζ) M) (nonToricPoint (Rz K ζ) M 1 1).1 (nonToricPoint (Rz K ζ) M 1 1).2
      (nonToricPoint (Rz K ζ) M 1 (M - 1)).1 (nonToricPoint (Rz K ζ) M 1 (M - 1)).2 := by
  classical
  let ι : Rz K ζ →+* Fz K ζ := algebraMap (Rz K ζ) (Fz K ζ)
  let ιL : LaurentSeries (Rz K ζ) →+* LaurentSeries (Fz K ζ) := coeffMap ι
  have hιinj : Function.Injective ι := IsFractionRing.injective (Rz K ζ) (Fz K ζ)
  have hιLinj : Function.Injective ιL := coeffMap_injective ι hιinj
  have hW : (tateBase (Rz K ζ) M).map ιL = tateBase (Fz K ζ) M := tateBase_map ι M
  have h1M : 1 < M := by omega
  have hxN : ∀ {j : ℕ}, 0 < j → j < M → ιL (nonToricPoint (Rz K ζ) M 1 j).1
      = (nonToricPoint (Fz K ζ) M 1 j).1 := fun {j} hj hjM => (coeffMap_nonToricPoint_one M ι hj hjM).1
  have hyN : ∀ {j : ℕ}, 0 < j → j < M → ιL (nonToricPoint (Rz K ζ) M 1 j).2
      = (nonToricPoint (Fz K ζ) M 1 j).2 := fun {j} hj hjM => (coeffMap_nonToricPoint_one M ι hj hjM).2

  obtain ⟨hBF, hB'F, hsum⟩ :=
    (ModularCurve.toricPoint_add_nonToricPoint_of_charZero (Fz K ζ) M).2.2 1 1 one_pos h1M
  have hB'F' : (tateBase (Fz K ζ) M).toAffine.Nonsingular (nonToricPoint (Fz K ζ) M 1 (M - 1)).1
      (nonToricPoint (Fz K ζ) M 1 (M - 1)).2 := by simpa only [inv_one] using hB'F
  have hsum' : (Point.some (nonToricPoint (Fz K ζ) M 1 1).1 (nonToricPoint (Fz K ζ) M 1 1).2 hBF :
      (tateBase (Fz K ζ) M).toAffine.Point)
      + Point.some (nonToricPoint (Fz K ζ) M 1 (M - 1)).1 (nonToricPoint (Fz K ζ) M 1 (M - 1)).2 hB'F'
      = 0 := by
    rw [← hsum]; congr 1
  have h : negRel ((tateBase (Rz K ζ) M).map ιL) (ιL (nonToricPoint (Rz K ζ) M 1 1).1)
      (ιL (nonToricPoint (Rz K ζ) M 1 1).2) (ιL (nonToricPoint (Rz K ζ) M 1 (M - 1)).1)
      (ιL (nonToricPoint (Rz K ζ) M 1 (M - 1)).2) := by
    rw [hW, hxN one_pos h1M, hyN one_pos h1M, hxN (by omega) (by omega), hyN (by omega) (by omega)]
    exact negRel_of_add_eq_zero hsum'
  exact negRel_of_map ιL _ hιLinj h

theorem relations_K_toric (hM : 2 ≤ M) (ζu : Kˣ) (hζu : (ζu : K) = ζ) (hζ1 : ζ ≠ 1) :
    (tateBase K M).toAffine.Equation (toricPoint K M ζ).1 (toricPoint K M ζ).2 ∧
    chordRel (tateBase K M) (toricPoint K M ζ).1 (toricPoint K M ζ).2
      (nonToricPoint K M 1 1).1 (nonToricPoint K M 1 1).2
      (nonToricPoint K M ζu 1).1 (nonToricPoint K M ζu 1).2 := by
  have hζ0 : ζ ≠ 0 := by rw [← hζu]; exact ζu.ne_zero
  let σ : Rz K ζ →+* K := spec K ζ
  let σL : LaurentSeries (Rz K ζ) →+* LaurentSeries K := coeffMap σ
  have hW : (tateBase (Rz K ζ) M).map σL = tateBase K M := tateBase_map σ M
  have h1M : 1 < M := by omega
  have hmapc : Units.map (σ : Rz K ζ →* K) (cX K hζ0) = ζu := by
    ext; rw [Units.coe_map, MonoidHom.coe_coe, spec_cX, hζu]
  have hmapc1 : Units.map (σ : Rz K ζ →* K) (cX K hζ0 * 1) = ζu := by rw [mul_one, hmapc]
  have hxA : σL (tateToricPoint (Rz K ζ) M (cX K hζ0)).1 = (toricPoint K M ζ).1 := by
    rw [show σL (tateToricPoint (Rz K ζ) M (cX K hζ0)).1 = _ from
      coeffMap_tateToricPoint_fst σ M _ (isUnit_one_sub_cX K hζ0 hζ1), hmapc,
      tateToricPoint_eq_toricPoint, hζu]
  have hyA : σL (tateToricPoint (Rz K ζ) M (cX K hζ0)).2 = (toricPoint K M ζ).2 := by
    rw [show σL (tateToricPoint (Rz K ζ) M (cX K hζ0)).2 = _ from
      coeffMap_tateToricPoint_snd σ M _ (isUnit_one_sub_cX K hζ0 hζ1), hmapc,
      tateToricPoint_eq_toricPoint, hζu]
  obtain ⟨hxB, hyB⟩ := coeffMap_nonToricPoint_one M σ (R := Rz K ζ) (S := K) one_pos h1M
  have hxC : σL (nonToricPoint (Rz K ζ) M (cX K hζ0 * 1) 1).1 = (nonToricPoint K M ζu 1).1 := by
    rw [show σL (nonToricPoint (Rz K ζ) M (cX K hζ0 * 1) 1).1 = _ from
      coeffMap_nonToricPoint_fst σ M _ 1 one_pos h1M, hmapc1]
  have hyC : σL (nonToricPoint (Rz K ζ) M (cX K hζ0 * 1) 1).2 = (nonToricPoint K M ζu 1).2 := by
    rw [show σL (nonToricPoint (Rz K ζ) M (cX K hζ0 * 1) 1).2 = _ from
      coeffMap_nonToricPoint_snd σ M _ 1 one_pos h1M, hmapc1]
  obtain ⟨heq, hchord⟩ := relations_R_toric K M hM hζ0 hζ1
  refine ⟨?_, ?_⟩
  · have h : ((tateBase (Rz K ζ) M).map σL).toAffine.Equation
        (σL (tateToricPoint (Rz K ζ) M (cX K hζ0)).1) (σL (tateToricPoint (Rz K ζ) M (cX K hζ0)).2) :=
      heq.map σL
    rw [hW, hxA, hyA] at h
    exact h
  · have h := chordRel_map σL _ hchord
    rw [hW, hxA, hyA, hxB, hyB, hxC, hyC] at h
    exact h

theorem relations_K_line {k : ℕ} (hk : 1 ≤ k) (hkM : 1 + k < M) :
    (2 ≤ k → chordRel (tateBase K M) (nonToricPoint K M 1 1).1 (nonToricPoint K M 1 1).2
        (nonToricPoint K M 1 k).1 (nonToricPoint K M 1 k).2
        (nonToricPoint K M 1 (1 + k)).1 (nonToricPoint K M 1 (1 + k)).2) ∧
    (k = 1 → dblRel (tateBase K M) (nonToricPoint K M 1 1).1 (nonToricPoint K M 1 1).2
        (nonToricPoint K M 1 (1 + k)).1 (nonToricPoint K M 1 (1 + k)).2) := by
  let σ : Rz K (0 : K) →+* K := spec K 0
  let σL : LaurentSeries (Rz K (0 : K)) →+* LaurentSeries K := coeffMap σ
  have hW : (tateBase (Rz K (0 : K)) M).map σL = tateBase K M := tateBase_map σ M
  have hxN : ∀ {j : ℕ}, 0 < j → j < M → σL (nonToricPoint (Rz K (0 : K)) M 1 j).1
      = (nonToricPoint K M 1 j).1 := fun {j} hj hjM => (coeffMap_nonToricPoint_one M σ hj hjM).1
  have hyN : ∀ {j : ℕ}, 0 < j → j < M → σL (nonToricPoint (Rz K (0 : K)) M 1 j).2
      = (nonToricPoint K M 1 j).2 := fun {j} hj hjM => (coeffMap_nonToricPoint_one M σ hj hjM).2
  have h1M : 1 < M := by omega
  have hkM' : k < M := by omega
  obtain ⟨hchord, hdbl⟩ := relations_R_line K M (ζ := (0 : K)) hk hkM
  refine ⟨fun hk2 => ?_, fun hk1 => ?_⟩
  · have h := chordRel_map σL _ (hchord hk2)
    rw [hW, hxN one_pos h1M, hyN one_pos h1M, hxN (by omega) hkM', hyN (by omega) hkM',
      hxN (by omega) hkM, hyN (by omega) hkM] at h
    exact h
  · have h := dblRel_map σL _ (hdbl hk1)
    rw [hW, hxN one_pos h1M, hyN one_pos h1M, hxN (by omega) hkM, hyN (by omega) hkM] at h
    exact h

theorem relations_K_inv (hM : 2 ≤ M) :
    negRel (tateBase K M) (nonToricPoint K M 1 1).1 (nonToricPoint K M 1 1).2
      (nonToricPoint K M 1 (M - 1)).1 (nonToricPoint K M 1 (M - 1)).2 := by
  let σ : Rz K (0 : K) →+* K := spec K 0
  let σL : LaurentSeries (Rz K (0 : K)) →+* LaurentSeries K := coeffMap σ
  have hW : (tateBase (Rz K (0 : K)) M).map σL = tateBase K M := tateBase_map σ M
  have hxN : ∀ {j : ℕ}, 0 < j → j < M → σL (nonToricPoint (Rz K (0 : K)) M 1 j).1
      = (nonToricPoint K M 1 j).1 := fun {j} hj hjM => (coeffMap_nonToricPoint_one M σ hj hjM).1
  have hyN : ∀ {j : ℕ}, 0 < j → j < M → σL (nonToricPoint (Rz K (0 : K)) M 1 j).2
      = (nonToricPoint K M 1 j).2 := fun {j} hj hjM => (coeffMap_nonToricPoint_one M σ hj hjM).2
  have h1M : 1 < M := by omega
  have h := negRel_map σL _ (relations_R_inv K M (ζ := (0 : K)) hM)
  rw [hW, hxN one_pos h1M, hyN one_pos h1M, hxN (by omega) (by omega),
    hyN (by omega) (by omega)] at h
  exact h

end Descent

section Assembly

variable (K : Type u) [Field K] [DecidableEq (LaurentSeries K)] (M : ℕ) [NeZero M]

theorem tateBase_a₁ : (tateBase K M).a₁ = 1 := by
  simp [tateBase, tateLaurent, tatePowerSeries]

theorem tateBase_a₃ : (tateBase K M).a₃ = 0 := by
  simp [tateBase, tateLaurent, tatePowerSeries]

theorem tateBase_map_qTwist (ζ : Kˣ) (hζM : ζ ^ M = 1) :
    (tateBase K M).map (qTwist ζ) = tateBase K M := by
  have h : (qTwist ζ).comp (qExpand K M) = qExpand K M := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, qTwist_qExpand, zpow_natCast, hζM, qTwist_one_apply]
  rw [tateBase, WeierstrassCurve.map_map, h]

theorem qTwist_eq_self_of_coeff (ζ : Kˣ) (hζM : ζ ^ M = 1) (f : LaurentSeries K)
    (hf : ∀ k : ℤ, ¬ (M : ℤ) ∣ k → f.coeff k = 0) : qTwist ζ f = f := by
  ext k
  rw [qTwist_coeff]
  by_cases hk : (M : ℤ) ∣ k
  · obtain ⟨t, rfl⟩ := hk
    rw [zpow_mul, zpow_natCast, hζM, one_zpow, Units.val_one, one_mul]
  · rw [hf k hk, mul_zero]

theorem main (hM : 2 ≤ M) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M) :
    ∃ (xA yA xB yB : LaurentSeries K)
      (hA : (tateBase K M).toAffine.Nonsingular xA yA)
      (hB : (tateBase K M).toAffine.Nonsingular xB yB)
      (hB' : (tateBase K M).toAffine.Nonsingular (qTwist ζ xB) (qTwist ζ yB)),
      M • (Point.some xA yA hA) = 0 ∧ M • (Point.some xB yB hB) = 0 ∧
      (∀ a b : ℤ, a • Point.some xA yA hA + b • Point.some xB yB hB = 0 →
        (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧
      qTwist ζ xA = xA ∧ qTwist ζ yA = yA ∧
      Point.some (qTwist ζ xB) (qTwist ζ yB) hB' = Point.some xA yA hA + Point.some xB yB hB := by

  set E : WeierstrassCurve (LaurentSeries K) := tateBase K M with hEdef
  set z : K := (ζ : K) with hz
  have hM0 : M ≠ 0 := by omega
  have h1M : 1 < M := by omega
  have hz0 : z ≠ 0 := ζ.ne_zero
  have hpow : ∀ {n : ℕ}, z ^ n = 1 ↔ M ∣ n := fun {n} => hζ.pow_eq_one_iff_dvd n
  have hz1 : z ≠ 1 := by
    intro h; have h2 : M ∣ 1 := hpow.mp (by rw [pow_one, h]); exact absurd (Nat.le_of_dvd one_pos h2) (by omega)
  have hζM : ζ ^ M = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hζ.pow_eq_one)
  haveI hMK : NeZero ((M : ℕ) : K) := hζ.neZero'

  set xA : LaurentSeries K := (toricPoint K M z).1 with hxA
  set yA : LaurentSeries K := (toricPoint K M z).2 with hyA
  set xN : ℕ → LaurentSeries K := fun k => (nonToricPoint K M 1 k).1 with hxN
  set yN : ℕ → LaurentSeries K := fun k => (nonToricPoint K M 1 k).2 with hyN
  set xC : LaurentSeries K := (nonToricPoint K M ζ 1).1 with hxC
  set yC : LaurentSeries K := (nonToricPoint K M ζ 1).2 with hyC

  obtain ⟨heqA, hchordA⟩ := relations_K_toric K M hM ζ rfl hz1
  have hA : E.toAffine.Nonsingular xA yA := equation_iff_nonsingular.mp heqA
  have hN : ∀ {k : ℕ}, 0 < k → k < M → E.toAffine.Nonsingular (xN k) (yN k) := fun {k} hk hkM =>
    equation_iff_nonsingular.mp (equation_tateBase_nonToricPoint K M 1 k hk hkM)
  have hB : E.toAffine.Nonsingular (xN 1) (yN 1) := hN one_pos h1M
  have hC : E.toAffine.Nonsingular xC yC :=
    equation_iff_nonsingular.mp (equation_tateBase_nonToricPoint K M ζ 1 one_pos h1M)

  have htwB : qTwist ζ (xN 1) = xC ∧ qTwist ζ (yN 1) = yC := by
    have h := qTwist_nonToricPoint_of_pow_eq_one K M ζ hζM 1 1 one_pos h1M
    rw [pow_one, one_mul] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hB' : E.toAffine.Nonsingular (qTwist ζ (xN 1)) (qTwist ζ (yN 1)) := by
    rw [htwB.1, htwB.2]; exact hC
  have hfixA : qTwist ζ xA = xA ∧ qTwist ζ yA = yA :=
    ⟨qTwist_eq_self_of_coeff K M ζ hζM xA fun k hk => (coeff_toricPoint_of_not_dvd K M z hk).1,
     qTwist_eq_self_of_coeff K M ζ hζM yA fun k hk => (coeff_toricPoint_of_not_dvd K M z hk).2⟩

  set A : E.toAffine.Point := Point.some xA yA hA with hAdef
  set B : E.toAffine.Point := Point.some (xN 1) (yN 1) hB with hBdef
  set C' : E.toAffine.Point := Point.some (qTwist ζ (xN 1)) (qTwist ζ (yN 1)) hB' with hC'def

  have hxAB : xA ≠ xN 1 := by
    intro h
    have h0 := congrArg (fun s : LaurentSeries K => s.coeff 0) h
    simp only [hxA, hxN, coeff_zero_toricPoint_fst, coeff_zero_nonToricPoint_fst M 1 1 one_pos h1M] at h0
    have h1 : (1 - z) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hz1))
    exact hz0 ((div_eq_zero_iff.mp h0).resolve_right h1)
  have hAB : A + B = C' := by
    rw [hAdef, hBdef, hC'def, add_eq_of_chordRel hchordA hxAB hA hB hC]
    exact point_some_congr htwB.1.symm htwB.2.symm _ _

  have hEmap : E.map (qTwist ζ) = E := tateBase_map_qTwist K M ζ hζM
  let τ : E.toAffine.Point →+ E.toAffine.Point := mapPt E E (qTwist ζ) (qTwist_injective ζ) hEmap
  have hτsome : ∀ (x y : LaurentSeries K) (h : E.toAffine.Nonsingular x y),
      ∃ h', τ (Point.some x y h) = Point.some (qTwist ζ x) (qTwist ζ y) h' :=
    fun x y h => ⟨_, rfl⟩
  have hτA : τ A = A := by
    obtain ⟨h', e⟩ := hτsome xA yA hA
    rw [hAdef, e]; exact point_some_congr hfixA.1 hfixA.2 _ _
  have hτB : τ B = A + B := by
    obtain ⟨h', e⟩ := hτsome (xN 1) (yN 1) hB
    rw [hAB, hBdef, e]
  have hiter : ∀ k : ℕ, (τ^[k]) B = k • A + B := by
    intro k
    induction k with
    | zero => rw [Function.iterate_zero_apply, zero_nsmul, zero_add]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_add, map_nsmul, hτA, hτB, succ_nsmul]; abel
  have hτpow : ∀ k : ℕ, ∃ h', (τ^[k]) B
      = Point.some (qTwist (ζ ^ k) (xN 1)) (qTwist (ζ ^ k) (yN 1)) h' := by
    intro k
    induction k with
    | zero =>
      refine ⟨by rw [pow_zero, qTwist_one_apply, qTwist_one_apply]; exact hB, ?_⟩
      rw [Function.iterate_zero_apply, hBdef]
      exact point_some_congr (by rw [pow_zero, qTwist_one_apply]) (by rw [pow_zero, qTwist_one_apply]) _ _
    | succ k ih =>
      obtain ⟨h', e⟩ := ih
      obtain ⟨h'', e'⟩ := hτsome _ _ h'
      refine ⟨by rw [pow_succ', ← qTwist_qTwist, ← qTwist_qTwist]; exact h'', ?_⟩
      rw [Function.iterate_succ_apply', e, e']
      exact point_some_congr (by rw [qTwist_qTwist, pow_succ']) (by rw [qTwist_qTwist, pow_succ']) _ _

  have hMA : M • A = 0 := by
    have h1 := hiter M
    obtain ⟨h', h2⟩ := hτpow M
    rw [h2] at h1
    have h3 : (Point.some (qTwist (ζ ^ M) (xN 1)) (qTwist (ζ ^ M) (yN 1)) h' : E.toAffine.Point) = B :=
      by rw [hBdef]; exact point_some_congr (by rw [hζM, qTwist_one_apply]) (by rw [hζM, qTwist_one_apply]) _ _
    rw [h3] at h1
    exact (add_eq_right.mp h1.symm)

  have hκ : (xN 1).coeff 1 ≠ 0 := by
    rw [hxN]
    show (nonToricPoint K M 1 1).1.coeff 1 ≠ 0
    rw [coeff_one_nonToricPoint_fst M 1 1 one_pos h1M, if_pos rfl, Units.val_one, inv_one, Units.val_one]
    by_cases h2 : 1 + 1 = M
    · rw [if_pos h2, one_add_one_eq_two]
      have hM2 : ((M : ℕ) : K) ≠ 0 := hMK.ne
      rw [← h2] at hM2
      push_cast at hM2
      exact hM2
    · rw [if_neg h2, add_zero]; exact one_ne_zero
  have hordA_nat : ∀ n : ℕ, n < M → n • A = 0 → n = 0 := by
    intro n hn h0
    have h1 := hiter n
    obtain ⟨h', h2⟩ := hτpow n
    rw [h0, zero_add, h2, hBdef] at h1
    have hx : qTwist (ζ ^ n) (xN 1) = xN 1 := (Point.some.inj h1).1
    have hc := congrArg (fun s : LaurentSeries K => s.coeff 1) hx
    simp only [qTwist_coeff, zpow_one] at hc
    have hzn : ((ζ ^ n : Kˣ) : K) = 1 := by
      have := mul_right_cancel₀ hκ (hc.trans (one_mul _).symm)
      exact this
    rw [Units.val_pow_eq_pow_val] at hzn
    have hdvd : M ∣ n := hpow.mp hzn
    rcases Nat.eq_zero_or_pos n with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd h hdvd) (by omega)
  have hordA : ∀ c : ℤ, c • A = 0 → (M : ℤ) ∣ c := by
    intro c hc
    have hMpos : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM0
    have hdecomp : c = M * (c / M) + c % M := (Int.mul_ediv_add_emod c M).symm
    have hlt : c % M < M := Int.emod_lt_of_pos c hMpos
    have hnn : 0 ≤ c % M := Int.emod_nonneg c (by exact_mod_cast hM0)
    set n : ℕ := (c % M).toNat with hn
    have hn' : (n : ℤ) = c % M := Int.toNat_of_nonneg hnn
    have hnM : n < M := by omega
    have hsm : n • A = 0 := by
      have h1 : c • A = (c / M) • ((M : ℤ) • A) + (c % M) • A := by
        conv_lhs => rw [hdecomp]
        rw [add_zsmul, mul_comm, mul_zsmul]
      rw [natCast_zsmul, hMA, zsmul_zero, zero_add, ← hn', natCast_zsmul] at h1
      rw [← h1]; exact hc
    have hn0 := hordA_nat n hnM hsm
    have hmod : c % M = 0 := by rw [← hn', hn0, Nat.cast_zero]
    exact Int.dvd_of_emod_eq_zero hmod

  have hneg2 : ∀ (x y : LaurentSeries K), E.toAffine.negY x y = -y - x := by
    intro x y; rw [negY, hEdef, tateBase_a₁, tateBase_a₃]; ring
  have hchordB : ∀ {k : ℕ} (hk2 : 2 ≤ k) (hkM : 1 + k < M),
      B + Point.some (xN k) (yN k) (hN (by omega) (by omega))
        = Point.some (xN (1 + k)) (yN (1 + k)) (hN (by omega) hkM) := by
    intro k hk2 hkM
    obtain ⟨hc, -⟩ := relations_K_line K M (by omega) hkM
    have hxne : xN 1 ≠ xN k := by
      intro h
      have h0 := congrArg (fun s : LaurentSeries K => s.coeff 1) h
      simp only [hxN, coeff_one_nonToricPoint_fst M 1 1 one_pos h1M,
        coeff_one_nonToricPoint_fst M 1 k (by omega) (by omega : k < M),
        if_neg (show ¬ 1 + 1 = M by omega), if_neg (show ¬ k = 1 by omega),
        if_neg (show ¬ k + 1 = M by omega), add_zero, Units.val_one] at h0
      exact one_ne_zero h0
    rw [hBdef]
    exact add_eq_of_chordRel (hc hk2) hxne _ _ _
  have hdblB : ∀ (h3 : 1 + 1 < M),
      B + B = Point.some (xN (1 + 1)) (yN (1 + 1)) (hN (by omega) h3) := by
    intro h3
    obtain ⟨-, hd⟩ := relations_K_line K M (k := 1) le_rfl h3
    rw [hBdef]
    refine add_eq_of_dblRel (hd rfl) ?_ _ _
    intro hy
    rw [hneg2] at hy
    have h0 := congrArg (fun s : LaurentSeries K => s.coeff 1) hy
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_neg,
      coeff_one_nonToricPoint_fst M 1 1 one_pos h1M, coeff_one_nonToricPoint_snd M 1 1 one_pos h1M,
      if_neg (show ¬ 1 + 1 = M by omega), add_zero, neg_zero, Units.val_one] at h0
    norm_num at h0
  have hinvB : B + Point.some (xN (M - 1)) (yN (M - 1)) (hN (by omega) (by omega)) = 0 := by
    obtain ⟨hx, hy⟩ := relations_K_inv K M hM
    rw [hBdef]
    refine Point.add_of_Y_eq hx.symm ?_
    show (nonToricPoint K M 1 1).2 = (tateBase K M).toAffine.negY (nonToricPoint K M 1 (M - 1)).1
      (nonToricPoint K M 1 (M - 1)).2
    rw [hx, hy, negY_negY]
  have hladder : ∀ k : ℕ, ∀ (hk : 1 ≤ k) (hkM : k < M),
      k • B = Point.some (xN k) (yN k) (hN (by omega) hkM) := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro hk hkM
      rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · have hk0' : k = 0 := by omega
        subst hk0'
        rw [one_nsmul, hBdef]
      · rw [succ_nsmul, ih hk1 (by omega)]
        by_cases hk1' : k = 1
        · subst hk1'
          rw [show (Point.some (xN 1) (yN 1) (hN (by omega) (by omega : 1 < M)) : E.toAffine.Point) = B
            from by rw [hBdef]]
          exact hdblB (by omega)
        · rw [add_comm]
          have h := hchordB (k := k) (by omega) (by omega)
          rw [h]
          exact point_some_congr (by rw [add_comm]) (by rw [add_comm]) _ _
  have hMB : M • B = 0 := by
    have h : M = (M - 1) + 1 := by omega
    conv_lhs => rw [h]
    rw [succ_nsmul, hladder (M - 1) (by omega) (by omega)]
    rw [add_comm]; exact hinvB

  have hindep : ∀ a b : ℤ, a • A + b • B = 0 → (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b := by
    intro a b hab
    have h1 : τ (a • A + b • B) = 0 := by rw [hab, map_zero]
    rw [map_add, map_zsmul, map_zsmul, hτA, hτB, zsmul_add] at h1
    have hbA : b • A = 0 := by
      have h2 : a • A + (b • A + b • B) = (a • A + b • B) + b • A := by abel
      rw [h2, hab, zero_add] at h1
      exact h1
    have hb : (M : ℤ) ∣ b := hordA b hbA
    have hbB : b • B = 0 := by
      obtain ⟨t, rfl⟩ := hb
      rw [mul_comm, mul_zsmul, natCast_zsmul, hMB, zsmul_zero]
    have haA : a • A = 0 := by rwa [hbB, add_zero] at hab
    exact ⟨hordA a haA, hb⟩
  refine ⟨xA, yA, xN 1, yN 1, hA, hB, hB', hMA, hMB, hindep, hfixA.1, hfixA.2, hAB.symm⟩

end Assembly

end P2MTateInertia
p2m_reactivate "P2MW.S_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot.ModularCurve.P2MTateInertia"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot.ModularCurve.P2MTateInertia P2MW.S_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot.ModularCurve.P2MTateInertia P2MW.S_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot.ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot.ModularCurve WeierstrassCurve~Coeff WeierstrassCurve.Affine"

universe u in
theorem solution
    (K : Type u) [Field K] [DecidableEq (LaurentSeries K)] (M : ℕ) [NeZero M] (hM : 2 ≤ M)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M) :
    ∃ (xA yA xB yB : LaurentSeries K)
      (hA : (tateBase K M).toAffine.Nonsingular xA yA)
      (hB : (tateBase K M).toAffine.Nonsingular xB yB)
      (hB' : (tateBase K M).toAffine.Nonsingular (qTwist ζ xB) (qTwist ζ yB)),
      M • (Point.some xA yA hA) = 0 ∧ M • (Point.some xB yB hB) = 0 ∧
      (∀ a b : ℤ, a • Point.some xA yA hA + b • Point.some xB yB hB = 0 →
        (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧
      qTwist ζ xA = xA ∧ qTwist ζ yA = yA ∧
      Point.some (qTwist ζ xB) (qTwist ζ yB) hB' = Point.some xA yA hA + Point.some xB yB hB :=
  ModularCurve.P2MTateInertia.main K M hM ζ hζ

end S_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot
end P2MW
export P2MW.S_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot (solution)

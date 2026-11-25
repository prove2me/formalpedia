-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.relNorm_XYIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:37.608865+00:00
-- url     : https://prove2.me/submissions/75a28340-326f-430a-ba64-2f2ee4ac0305

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Theorems.Thm_GroundTheory_Arith_Abelian_finrank_coordinateRing
import Theorems.Thm_GroundTheory_Arith_Abelian_XIdeal_eq_map
import Theorems.Thm_GroundTheory_Arith_Abelian_span_X_sub_C_le_comap_XYIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable [IsAlgClosed F] [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {x y : F} (h : W.toAffine.Nonsingular x y) :
    Ideal.relNorm F[X] (XYIdeal W.toAffine x (C y)) = Ideal.span {X - C x} := by
  have hq : (Ideal.span {X - C x} : Ideal F[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C x)
  have hle : ∀ {y' : F}, W.toAffine.Nonsingular x y' →
      Ideal.relNorm F[X] (XYIdeal W.toAffine x (C y')) ≤ Ideal.span {X - C x} := by
    intro y' h'
    refine (Ideal.relNorm_le_comap F[X] _).trans ?_
    exact (hq.eq_of_le (Ideal.comap_ne_top _ (isMaximal_XYIdeal h'.1).ne_top)
      (span_X_sub_C_le_comap_XYIdeal W x (C y'))).ge
  have hmul : Ideal.relNorm F[X] (XYIdeal W.toAffine x (C (W.toAffine.negY x y))) *
      Ideal.relNorm F[X] (XYIdeal W.toAffine x (C y)) = Ideal.span {X - C x} ^ 2 := by
    rw [← map_mul, XYIdeal_neg_mul h, XIdeal_eq_map, Ideal.relNorm_algebraMap,
      finrank_coordinateRing]
  obtain ⟨a, ha⟩ := Ideal.dvd_iff_le.mpr (hle h)
  obtain ⟨b, hb⟩ := Ideal.dvd_iff_le.mpr (hle ((nonsingular_neg ..).mpr h))
  rw [ha, hb, pow_two] at hmul
  have hq0 : (Ideal.span {X - C x} : Ideal F[X]) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact X_sub_C_ne_zero x
  have hba : b * a = 1 := by
    refine mul_left_cancel₀ (mul_ne_zero hq0 hq0) ?_
    calc Ideal.span {X - C x} * Ideal.span {X - C x} * (b * a)
        = Ideal.span {X - C x} * b * (Ideal.span {X - C x} * a) := by ring
      _ = _ := hmul
      _ = _ := (mul_one _).symm
  have ha1 : a = 1 := by
    rw [Ideal.one_eq_top] at hba ⊢
    exact eq_top_iff.mpr (by rw [← hba, mul_comm]; exact Ideal.mul_le_left)
  rw [ha, ha1, mul_one]
end GroundTheory.Arith.Abelian

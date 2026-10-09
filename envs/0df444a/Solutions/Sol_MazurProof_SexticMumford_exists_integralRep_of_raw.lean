-- Prove2me | solution 1 for MazurProof.SexticMumford.exists_integralRep_of_raw
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:51:29.416437+00:00
-- url     : https://prove2.me/submissions/38c95bde-d926-48f4-8a99-805cb31aa723

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.SexticMumfordNormalForm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordNormalForm =====
section
/-!
# First normalization step for sextic Mumford ideals

Before choosing a two-generator `K[X]`-basis, a fractional ideal may be
cleared of denominators by a single nonzero element of the coordinate ring.
This is the first, representation-independent step in the normal-form
argument.
-/
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
/-- Every invertible fractional ideal of the sextic coordinate ring becomes
an integral ideal after multiplication by one nonzero principal factor. -/
theorem invFrac_exists_integral_scaling (M : Model K) (I : InvFrac M) :
    ∃ (a : CoordinateRing M) (J : Ideal (CoordinateRing M)), a ≠ 0 ∧
      (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
        FractionalIdeal.spanSingleton (CoordinateRing M)⁰
          (algebraMap (CoordinateRing M) (FunctionField M) a)⁻¹ * J := by
  exact FractionalIdeal.exists_eq_spanSingleton_mul
    (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordRepresentative =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordRepresentative =====
section
/-!
# Integral representatives of oriented sextic Picard classes

The balanced Mumford theorem has two logically separate steps.

1. Clear the denominator of an arbitrary invertible fractional ideal.
2. Reduce the resulting integral ideal to a Mumford ideal of degree at most
   the genus.

This file proves the first step for every oriented Picard class and proves
the quadratic Hermite normal form for every primitive integral ideal.  It
uses only structural fractional-ideal and PID theorems, and therefore does
not enumerate ideal classes.  The final theorem isolates balanced reduction
as the exact remaining surjectivity criterion for `classOf`.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)
namespace IntegralOrientedRep
end IntegralOrientedRep
/-- Every raw oriented fractional ideal is equivalent, modulo a principal
oriented ideal, to one with an integral finite component. -/
theorem exists_integralRep_of_raw (I : InvFrac M)
    (n : Multiplicative ℤ) :
    ∃ R : IntegralOrientedRep M,
      QuotientGroup.mk' (principalOriented M O).range (I, n) =
        Additive.toMul (R.picClass M O) := by
  obtain ⟨a, J, ha, hI⟩ := invFrac_exists_integral_scaling M I
  have haMap :
      algebraMap (CoordinateRing M) (FunctionField M) a ≠ 0 := by
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (show a ∈ (CoordinateRing M)⁰ from
        mem_nonZeroDivisors_iff_ne_zero.mpr ha)
  let alpha : (FunctionField M)ˣ :=
    Units.mk0
      (algebraMap (CoordinateRing M) (FunctionField M) a) haMap
  let U : InvFrac M :=
    I * toPrincipalIdeal (CoordinateRing M) (FunctionField M) alpha
  have hU :
      (U :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = J := by
    simp only [U, Units.val_mul, coe_toPrincipalIdeal, alpha,
      Units.val_mk0]
    rw [hI]
    calc
      (FractionalIdeal.spanSingleton (CoordinateRing M)⁰
            (algebraMap (CoordinateRing M) (FunctionField M) a)⁻¹ *
          (J :
            FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))) *
          FractionalIdeal.spanSingleton (CoordinateRing M)⁰
            (algebraMap (CoordinateRing M) (FunctionField M) a) =
        (FractionalIdeal.spanSingleton (CoordinateRing M)⁰
              (algebraMap (CoordinateRing M) (FunctionField M) a)⁻¹ *
            FractionalIdeal.spanSingleton (CoordinateRing M)⁰
              (algebraMap (CoordinateRing M) (FunctionField M) a)) *
          (J :
            FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
              ac_rfl
      _ = J := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
        simp [haMap]
  let R : IntegralOrientedRep M :=
    { ideal := J
      unit := U
      coe_unit := hU
      atInfinity :=
        Multiplicative.toAdd (n * O.ordPlus alpha) }
  refine ⟨R, ?_⟩
  change
    QuotientGroup.mk' (principalOriented M O).range (I, n) =
      QuotientGroup.mk' (principalOriented M O).range
        (U, Multiplicative.ofAdd R.atInfinity)
  have hprincipal :
      QuotientGroup.mk' (principalOriented M O).range
          (principalOriented M O alpha) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff
      (principalOriented M O alpha)).2
      (MonoidHom.mem_range.mpr ⟨alpha, rfl⟩)
  calc
    QuotientGroup.mk' (principalOriented M O).range (I, n) =
        QuotientGroup.mk' (principalOriented M O).range
          ((I, n) * principalOriented M O alpha) := by
            rw [map_mul, hprincipal]; exact (mul_one (QuotientGroup.mk' (principalOriented M O).range (I, n))).symm
    _ = QuotientGroup.mk' (principalOriented M O).range
          (U, Multiplicative.ofAdd R.atInfinity) := by
            rfl
end
end MazurProof.SexticMumford
end

end

theorem solution : type_of% @MazurProof.SexticMumford.exists_integralRep_of_raw := @MazurProof.SexticMumford.exists_integralRep_of_raw

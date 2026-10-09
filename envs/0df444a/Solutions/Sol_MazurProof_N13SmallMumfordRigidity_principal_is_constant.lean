-- Prove2me | solution 1 for MazurProof.N13SmallMumfordRigidity.principal_is_constant
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:47:51.407348+00:00
-- url     : https://prove2.me/submissions/12385f44-df32-4a8e-9dcb-c8d6fb978b47

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13BranchLeading_branch_min_order
import Theorems.Thm_MazurProof_N13BranchNorm_evalPoly_ne_zero
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_ker_mumfordEval
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_ker_mumfordEval
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_recompose
import Theorems.Thm_MazurProof_SexticMumford_ker_mumfordEval
import Theorems.Thm_MazurProof_SexticMumford_recompose

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13Infinity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13Infinity =====
section
/-!
# The positive infinity of the N13 genus-two curve

We construct the chosen branch at infinity inside `K((s))`.  With `x=s⁻¹`,
the equation becomes

`(s³ y)² = 1 + 4s + 6s² + 2s³ + s⁴ + 2s⁵ + s⁶`.

The square root with constant coefficient `+1` is obtained from the formal
binomial series.  The resulting embedding of the function field supplies the
integer orientation used in `SexticMumford`.
-/
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
/-! ## The formal positive square root -/
/-! ## An algebraic model of the function field -/
/-! ## The branch `x = s⁻¹`, `s³y = +sqrt(reverseF)` -/
theorem functionFieldToLaurent_injective :
    Function.Injective (functionFieldToLaurent K) :=
  (functionFieldToLaurent K).injective
end
end MazurProof.N13Infinity
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdeal =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdeal =====
section
/-!
# Mumford evaluation ideals for a smooth sextic affine ring

For a model `Y² = f(X)`, quotient evaluation `X ↦ X mod u`, `Y ↦ v mod u`
has kernel exactly `(u, Y - v)`.  This recovers canonical Mumford
polynomials from their ideal and is the algebraic core of normal-form
uniqueness.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
theorem mumfordIdeal_comap_base (D : SemiMumford M) :
    (mumfordIdeal M D.u D.v).comap (xClassHom M) =
      Ideal.span ({D.u} : Set K[X]) := by
  rw [← ker_mumfordEval]
  ext p
  simp only [Ideal.mem_comap, RingHom.mem_ker, xClassHom_apply,
    mumfordEval_xClass,
    Ideal.Quotient.eq_zero_iff_mem]
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordNorm =====
section
/-!
# Structural identities for the quadratic norm

The hyperelliptic norm is multiplicative, fixes the polynomial subring, and
can be read off from the two canonical coefficients.  These facts are kept
separate from any curve-specific degree calculation.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
theorem xClass_injective (M : Model K) :
    Function.Injective (xClass M) := by
  intro p q hpq
  by_contra hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  exact xClass_ne_zero M hsub (by
    rw [xClass_sub, hpq, sub_self])
@[simp] theorem coeffY_ySubClass (M : Model K) (v : K[X]) :
    coeffY M (ySubClass M v) = 1 := by
  simp [ySubClass]
theorem dvd_of_xClass_mul_ySubClass_mem_span
    (M : Model K) (u a v : K[X])
    (h : xClass M a * ySubClass M v ∈
      Ideal.span ({xClass M u} : Set (CoordinateRing M))) :
    u ∣ a := by
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨t, ht⟩ := h
  refine ⟨coeffY M t, ?_⟩
  have hc := congrArg (coeffY M) ht
  rw [coeffY_xClass_mul, coeffY_ySubClass, mul_one,
    coeffY_xClass_mul] at hc
  exact hc
theorem u_dvd_of_scaled_mumfordIdeal_eq
    (M : Model K) (u₁ v₁ u₂ v₂ : K[X])
    (h :
      mumfordIdeal M u₁ v₁ *
          Ideal.span ({xClass M u₂} : Set (CoordinateRing M)) =
        mumfordIdeal M u₂ v₂ *
          Ideal.span ({xClass M u₁} : Set (CoordinateRing M))) :
    u₁ ∣ u₂ := by
  have hyv :
      ySubClass M v₁ ∈ mumfordIdeal M u₁ v₁ :=
    Ideal.subset_span (by simp)
  have hu :
      xClass M u₂ ∈
        Ideal.span ({xClass M u₂} : Set (CoordinateRing M)) :=
    Ideal.subset_span (by simp)
  have hmem :
      ySubClass M v₁ * xClass M u₂ ∈
        mumfordIdeal M u₁ v₁ *
          Ideal.span ({xClass M u₂} : Set (CoordinateRing M)) :=
    Ideal.mul_mem_mul hyv hu
  rw [h] at hmem
  have hspan :
      xClass M u₂ * ySubClass M v₁ ∈
        Ideal.span ({xClass M u₁} : Set (CoordinateRing M)) := by
    rw [mul_comm]
    exact Ideal.mul_le_right hmem
  exact dvd_of_xClass_mul_ySubClass_mem_span M u₁ u₂ v₁ hspan
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.N13FactorRigidity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FactorRigidity =====
section
/-!
# Small-factor rigidity on the `X₁(13)` sextic

Suppose two affine functions multiply to a polynomial of degree at most two
and neither has more than a simple pole at the positive infinity.  Then both
functions lie in the polynomial subring and have degree at most one.

The proof does not compare coefficients.  It uses the quadratic norm and both
infinity branches.  A nonzero `Y`-part forces pole degree at least three; the
two norm-degree inequalities then contradict the degree of the product.
-/
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13FactorRigidity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem minus_order_le_neg_three_of_coeffY_ne_zero
    (p q : K[X])
    (hz : N13BranchNorm.linearFunction K p q ≠ 0)
    (hq : q ≠ 0)
    (hplus : (-2 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K
        (N13BranchNorm.linearFunction K p q)).order) :
    (N13InfinityMinus.coordinateToLaurentMinus K
      (N13BranchNorm.linearFunction K p q)).order ≤ -3 := by
  have hmin :=
    N13BranchLeading.branch_min_order K p q hz
  have hpole :
      3 ≤ N13BranchLeading.poleDegree K p q := by
    simp only [N13BranchLeading.poleDegree, hq, if_false]
    omega
  omega
/-- If two affine functions with at most double poles at the positive
infinity multiply to a polynomial of degree at most four, neither function
has a `Y`-part.  If both had a `Y`-part, both negative-branch pole orders
would be at most `-3`, whereas their product has pole order at least `-4`.
Once one `Y`-part vanishes, the rank-two coefficient decomposition forces
the other to vanish as well. -/
theorem factor_pair_coeffY_eq_zero
    (z w : N13Mumford.CoordinateRing K) (P : K[X])
    (hP : P ≠ 0) (hdeg : P.natDegree ≤ 4)
    (hprod :
      z * w = SexticMumford.xClass (N13Mumford.model K) P)
    (hzplus : (-2 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K z).order)
    (hwplus : (-2 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K w).order) :
    SexticMumford.coeffY (N13Mumford.model K) z = 0 ∧
      SexticMumford.coeffY (N13Mumford.model K) w = 0 := by
  let M := N13Mumford.model K
  let pz := SexticMumford.coeff0 M z
  let qz := SexticMumford.coeffY M z
  let pw := SexticMumford.coeff0 M w
  let qw := SexticMumford.coeffY M w
  have hzlin : N13BranchNorm.linearFunction K pz qz = z :=
    SexticMumford.recompose M z
  have hwlin : N13BranchNorm.linearFunction K pw qw = w :=
    SexticMumford.recompose M w
  have hxP :
      SexticMumford.xClass M P ≠ 0 :=
    SexticMumford.xClass_ne_zero M hP
  have hzw : z * w ≠ 0 := by
    rw [hprod]
    exact hxP
  have hz : z ≠ 0 := left_ne_zero_of_mul hzw
  have hw : w ≠ 0 := right_ne_zero_of_mul hzw
  have hzMinus :
      N13InfinityMinus.coordinateToLaurentMinus K z ≠ 0 :=
    by simpa using
      (N13InfinityMinus.coordinateToLaurentMinus_injective K).ne hz
  have hwMinus :
      N13InfinityMinus.coordinateToLaurentMinus K w ≠ 0 :=
    by simpa using
      (N13InfinityMinus.coordinateToLaurentMinus_injective K).ne hw
  have hminusSum :
      (N13InfinityMinus.coordinateToLaurentMinus K z).order +
          (N13InfinityMinus.coordinateToLaurentMinus K w).order =
        -(P.natDegree : ℤ) := by
    have hmapped :=
      congrArg
        (N13InfinityMinus.coordinateToLaurentMinus K) hprod
    rw [map_mul,
      N13InfinityMinus.coordinateToLaurentMinus_xClass] at hmapped
    calc
      (N13InfinityMinus.coordinateToLaurentMinus K z).order +
            (N13InfinityMinus.coordinateToLaurentMinus K w).order =
          (N13InfinityMinus.coordinateToLaurentMinus K z *
            N13InfinityMinus.coordinateToLaurentMinus K w).order :=
        (HahnSeries.order_mul hzMinus hwMinus).symm
      _ = (N13BranchNorm.evalPoly K P).order := by
        rw [hmapped]
        rfl
      _ = -(P.natDegree : ℤ) :=
        N13BranchNorm.evalPoly_order K P hP
  have hone : qz = 0 ∨ qw = 0 := by
    by_contra hboth
    push Not at hboth
    have hzBound :=
      minus_order_le_neg_three_of_coeffY_ne_zero
        K pz qz (hzlin.trans_ne hz) hboth.1
          (by simpa only [hzlin] using hzplus)
    have hwBound :=
      minus_order_le_neg_three_of_coeffY_ne_zero
        K pw qw (hwlin.trans_ne hw) hboth.2
          (by simpa only [hwlin] using hwplus)
    rw [hzlin] at hzBound
    rw [hwlin] at hwBound
    have hdegZ : (P.natDegree : ℤ) ≤ 4 := by
      exact_mod_cast hdeg
    omega
  rcases hone with hqz | hqw
  · have hzpoly : z = SexticMumford.xClass M pz := by
      simpa [M, N13BranchNorm.linearFunction, hqz] using hzlin.symm
    have hpz : pz ≠ 0 := by
      intro hpz
      apply hz
      rw [hzpoly, hpz, SexticMumford.xClass_zero]
    have hcoeff : pz * qw = 0 := by
      have hcoeff' := congrArg (SexticMumford.coeffY M) hprod
      rw [hzpoly, SexticMumford.coeffY_xClass_mul] at hcoeff'
      simpa [M, qw] using hcoeff'
    exact ⟨hqz, (mul_eq_zero.mp hcoeff).resolve_left hpz⟩
  · have hwpoly : w = SexticMumford.xClass M pw := by
      simpa [M, N13BranchNorm.linearFunction, hqw] using hwlin.symm
    have hpw : pw ≠ 0 := by
      intro hpw
      apply hw
      rw [hwpoly, hpw, SexticMumford.xClass_zero]
    have hprod' :
        w * z = SexticMumford.xClass (N13Mumford.model K) P := by
      simpa [mul_comm] using hprod
    have hcoeff : pw * qz = 0 := by
      have hcoeff' := congrArg (SexticMumford.coeffY M) hprod'
      rw [hwpoly, SexticMumford.coeffY_xClass_mul] at hcoeff'
      simpa [M, qz] using hcoeff'
    exact ⟨(mul_eq_zero.mp hcoeff).resolve_left hpw, hqw⟩
end
end MazurProof.N13FactorRigidity
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordPrincipalNumerator =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordPrincipalNumerator =====
section
/-!
# Integral numerators from principal relations

For a principal relation between two Mumford ideals, multiplying the
principal generator by the first `u`-polynomial clears all affine
denominator.  The proof is ideal-theoretic: the first Mumford ideal times its
hyperelliptic conjugate is the principal ideal `(u)`.
-/
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
theorem exists_numerator_mem_of_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (α : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂) :
    ∃ z : CoordinateRing M,
      z ∈ mumfordIdeal M D₂.u D₂.v ∧
        algebraMap (CoordinateRing M) (FunctionField M) z =
        (α : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M)
            (xClass M D₁.u) := by
  have hx :
      algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₁.u) ∈
        (mumfordIdealUnit M D₁ :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
    rw [coe_mumfordIdealUnit]
    exact FractionalIdeal.mem_coeIdeal_of_mem (CoordinateRing M)⁰
      (xClass_mem_mumfordIdeal M D₁.u D₁.v)
  have hα :
      (α : FunctionField M) ∈
        (toPrincipalIdeal (CoordinateRing M) (FunctionField M) α :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  have hprod := FractionalIdeal.mul_mem_mul hx hα
  have hfrac := congrArg
    (fun U : InvFrac M =>
      (U : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))) h
  rw [Units.val_mul, coe_toPrincipalIdeal, coe_mumfordIdealUnit,
    coe_mumfordIdealUnit] at hfrac
  rw [coe_mumfordIdealUnit, coe_toPrincipalIdeal] at hprod
  rw [hfrac] at hprod
  obtain ⟨z, hzmem, hzeq⟩ :=
    (FractionalIdeal.mem_coeIdeal (CoordinateRing M)⁰).mp hprod
  exact ⟨z, hzmem, by simpa [mul_comm] using hzeq⟩
theorem reverse_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (α : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂) :
    mumfordIdealUnit M D₂ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α⁻¹ =
        mumfordIdealUnit M D₁ := by
  rw [← h]
  simp only [mul_assoc, map_inv, mul_inv_cancel, mul_one]
theorem exists_integral_factor_pair_of_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (α : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂) :
    ∃ z w : CoordinateRing M,
      z ∈ mumfordIdeal M D₂.u D₂.v ∧
      w ∈ mumfordIdeal M D₁.u D₁.v ∧
      z * w = xClass M (D₁.u * D₂.u) ∧
      algebraMap (CoordinateRing M) (FunctionField M) z =
        (α : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M)
            (xClass M D₁.u) ∧
      algebraMap (CoordinateRing M) (FunctionField M) w =
        (↑α⁻¹ : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M)
            (xClass M D₂.u) := by
  obtain ⟨z, hzmem, hzeq⟩ :=
    exists_numerator_mem_of_principal_relation M D₁ D₂ α h
  obtain ⟨w, hwmem, hweq⟩ :=
    exists_numerator_mem_of_principal_relation M D₂ D₁ α⁻¹
      (reverse_principal_relation M D₁ D₂ α h)
  refine ⟨z, w, hzmem, hwmem, ?_, hzeq, hweq⟩
  apply IsFractionRing.injective (CoordinateRing M) (FunctionField M)
  rw [map_mul, hzeq, hweq, xClass_mul, map_mul]
  change
    ((α : FunctionField M) *
        algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₁.u)) *
      ((↑α⁻¹ : FunctionField M) *
        algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₂.u)) =
      algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₁.u) *
        algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₂.u)
  rw [Units.val_inv_eq_inv_val]
  field_simp
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordPrincipalScale =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordPrincipalScale =====
section
/-!
# Cancelling a principal scale between Mumford ideals

If a principal fractional-ideal relation scales the first polynomial
generator to a unit multiple of the second, the associated integral
Mumford ideals satisfy the cross-multiplied equality.  Contracting that
equality to the polynomial subring recovers equality of the monic
`u`-polynomials.
-/
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u v
theorem scaled_ideal_eq_of_principal_scale
    {R : Type u} [CommRing R]
    {L : Type v} [Field L] [Algebra R L] [IsFractionRing R L]
    (I₁ I₂ : Ideal R) (α : Lˣ) (u₁ u₂ c d : R)
    (hIdeal :
      (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (α : L) = I₂)
    (hscale : (α : L) * algebraMap R L u₁ =
      algebraMap R L u₂ * algebraMap R L c)
    (hunit : c * d = 1) :
    I₁ * Ideal.span ({u₂} : Set R) =
      I₂ * Ideal.span ({u₁} : Set R) := by
  apply (FractionalIdeal.coeIdeal_inj (K := L)).mp
  have hc : IsUnit c := IsUnit.of_mul_eq_one d hunit
  have hspan_c :
      FractionalIdeal.spanSingleton R⁰ (algebraMap R L c) = 1 := by
    calc
      FractionalIdeal.spanSingleton R⁰ (algebraMap R L c) =
          (Ideal.span ({c} : Set R) : FractionalIdeal R⁰ L) :=
        (FractionalIdeal.coeIdeal_span_singleton c).symm
      _ = (⊤ : Ideal R) := by
        rw [Ideal.span_singleton_eq_top.mpr hc]
      _ = 1 := by simp
  calc
    ((I₁ * Ideal.span ({u₂} : Set R) : Ideal R) :
          FractionalIdeal R⁰ L) =
        (I₁ : FractionalIdeal R⁰ L) *
          (Ideal.span ({u₂} : Set R) : FractionalIdeal R⁰ L) :=
      FractionalIdeal.coeIdeal_mul I₁ (Ideal.span ({u₂} : Set R))
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₂) := by
      rw [FractionalIdeal.coeIdeal_span_singleton]
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₂) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L c) := by
      rw [hspan_c, mul_one]
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰
            (algebraMap R L u₂ * algebraMap R L c) := by
      rw [mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰
            ((α : L) * algebraMap R L u₁) := by
      rw [hscale]
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          (FractionalIdeal.spanSingleton R⁰ (α : L) *
            FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₁)) := by
      rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
    _ =
        ((I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (α : L)) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₁) := by
      rw [mul_assoc]
    _ =
        (I₂ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₁) := by
      rw [hIdeal]
    _ =
        (I₂ : FractionalIdeal R⁰ L) *
          (Ideal.span ({u₁} : Set R) : FractionalIdeal R⁰ L) := by
      rw [FractionalIdeal.coeIdeal_span_singleton]
    _ =
        ((I₂ * Ideal.span ({u₁} : Set R) : Ideal R) :
          FractionalIdeal R⁰ L) := by
      exact
        (FractionalIdeal.coeIdeal_mul I₂
          (Ideal.span ({u₁} : Set R))).symm
theorem mumford_u_eq_of_principal_scale
    {K : Type u} [Field K] (M : Model K)
    (D₁ D₂ : SemiMumford M) (α : (FunctionField M)ˣ)
    (c d : CoordinateRing M)
    (hIdeal :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂)
    (hscale :
      (α : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₁.u) =
        algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₂.u) *
          algebraMap (CoordinateRing M) (FunctionField M) c)
    (hunit : c * d = 1) :
    D₁.u = D₂.u := by
  have hfrac := congrArg
    (fun U : InvFrac M =>
      (U : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))) hIdeal
  rw [Units.val_mul, coe_toPrincipalIdeal,
    coe_mumfordIdealUnit, coe_mumfordIdealUnit] at hfrac
  have hscaled := scaled_ideal_eq_of_principal_scale
    (mumfordIdeal M D₁.u D₁.v)
    (mumfordIdeal M D₂.u D₂.v)
    α (xClass M D₁.u) (xClass M D₂.u) c d
    hfrac hscale hunit
  have h₁₂ := u_dvd_of_scaled_mumfordIdeal_eq
    M D₁.u D₁.v D₂.u D₂.v hscaled
  have h₂₁ := u_dvd_of_scaled_mumfordIdeal_eq
    M D₂.u D₂.v D₁.u D₁.v hscaled.symm
  exact Polynomial.eq_of_monic_of_associated D₁.u_monic D₂.u_monic
    (associated_of_dvd_dvd h₁₂ h₂₁)
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.N13SmallMumfordRigidity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SmallMumfordRigidity =====
section
/-!
# Rigidity of balanced Mumford representatives on `X₁(13)`

For balanced representatives, a principal relation clears to two affine
factors whose product has degree at most four.  The two-infinity pole-order
argument forces both factors into the polynomial subring.  Ideal
contraction then identifies the monic `u`-polynomials, so the principal
function is constant and the balanced representatives agree.

Together with structural infinity balancing, this gives the full unique
Mumford normal form and hence the Abel--Jacobi embedding of the curve,
without coefficient enumeration.
-/
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13SmallMumfordRigidity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
open SexticMumford
theorem numerator_order
    (α : (N13Mumford.FunctionField K)ˣ)
    (u : K[X]) (z : N13Mumford.CoordinateRing K)
    (hu : u ≠ 0)
    (hz :
      algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) z =
        (α : N13Mumford.FunctionField K) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K)
            (xClass (N13Mumford.model K) u)) :
    (N13Infinity.coordinateToLaurent K z).order =
      (N13Infinity.functionFieldToLaurent K
          (α : N13Mumford.FunctionField K)).order -
        (u.natDegree : ℤ) := by
  have hα :
      N13Infinity.functionFieldToLaurent K
          (α : N13Mumford.FunctionField K) ≠ 0 :=
    by simpa only [map_zero] using
      (N13Infinity.functionFieldToLaurent_injective K).ne α.ne_zero
  have huL : N13BranchNorm.evalPoly K u ≠ 0 :=
    N13BranchNorm.evalPoly_ne_zero K hu
  have hmapped := congrArg (N13Infinity.functionFieldToLaurent K) hz
  rw [map_mul, N13Infinity.functionFieldToLaurent_algebraMap,
    N13Infinity.functionFieldToLaurent_algebraMap,
    N13Infinity.coordinateToLaurent_xClass] at hmapped
  change
    N13Infinity.coordinateToLaurent K z =
      N13Infinity.functionFieldToLaurent K
          (α : N13Mumford.FunctionField K) *
        N13BranchNorm.evalPoly K u at hmapped
  calc
    (N13Infinity.coordinateToLaurent K z).order =
        (N13Infinity.functionFieldToLaurent K
            (α : N13Mumford.FunctionField K) *
          N13BranchNorm.evalPoly K u).order := by rw [hmapped]
    _ =
        (N13Infinity.functionFieldToLaurent K
            (α : N13Mumford.FunctionField K)).order +
          (N13BranchNorm.evalPoly K u).order :=
      HahnSeries.order_mul hα huL
    _ = _ := by
      rw [N13BranchNorm.evalPoly_order K u hu]
      omega
theorem inverse_order
    (α : (N13Mumford.FunctionField K)ˣ) :
    (N13Infinity.functionFieldToLaurent K
        (↑α⁻¹ : N13Mumford.FunctionField K)).order =
      -(N13Infinity.functionFieldToLaurent K
        (α : N13Mumford.FunctionField K)).order := by
  let a :=
    N13Infinity.functionFieldToLaurent K
      (α : N13Mumford.FunctionField K)
  let b :=
    N13Infinity.functionFieldToLaurent K
      (↑α⁻¹ : N13Mumford.FunctionField K)
  have ha : a ≠ 0 :=
    by simpa only [a, map_zero] using
      (N13Infinity.functionFieldToLaurent_injective K).ne α.ne_zero
  have hb : b ≠ 0 := by
    simpa only [b, map_zero] using
      (N13Infinity.functionFieldToLaurent_injective K).ne
        (Units.ne_zero α⁻¹)
  have hab : a * b = 1 := by
    simp [a, b]
  have hord := HahnSeries.order_mul ha hb
  rw [hab, HahnSeries.order_one] at hord
  change b.order = -a.order
  omega
theorem orientation_order
    (D₁ D₂ : Mumford (N13Mumford.model K))
    (α : (N13Mumford.FunctionField K)ˣ)
    (hInf :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) *
          (N13Infinity.positiveInfinityOrder K).ordPlus α =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1)) :
    (N13Infinity.functionFieldToLaurent K
        (α : N13Mumford.FunctionField K)).order =
      (D₂.nInf : ℤ) - D₁.nInf := by
  change
    Multiplicative.ofAdd
        (((D₁.nInf : ℤ) - 1) +
          (N13Infinity.functionFieldToLaurent K
            (α : N13Mumford.FunctionField K)).order) =
      Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1) at hInf
  have h := Multiplicative.ofAdd.injective hInf
  omega
theorem principal_is_constant
    (D₁ D₂ : Mumford (N13Mumford.model K))
    (α : (N13Mumford.FunctionField K)ˣ)
    (hIdeal :
      mumfordIdealUnit (N13Mumford.model K) D₁.toSemi *
          toPrincipalIdeal (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) α =
        mumfordIdealUnit (N13Mumford.model K) D₂.toSemi)
    (hInf :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) *
          (N13Infinity.positiveInfinityOrder K).ordPlus α =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1)) :
    ∃ c : Kˣ, α = N13Infinity.functionConstUnit K c := by
  let M := N13Mumford.model K
  obtain ⟨z, w, hzmem, hwmem, hprod, hzeq, hweq⟩ :=
    exists_integral_factor_pair_of_principal_relation
      M D₁.toSemi D₂.toSemi α hIdeal
  change z ∈ mumfordIdeal M D₂.u D₂.v at hzmem
  change w ∈ mumfordIdeal M D₁.u D₁.v at hwmem
  change z * w = xClass M (D₁.u * D₂.u) at hprod
  change
    algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K) z =
      (α : N13Mumford.FunctionField K) *
        algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M D₁.u) at hzeq
  change
    algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K) w =
      (↑α⁻¹ : N13Mumford.FunctionField K) *
        algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M D₂.u) at hweq
  have hu₁ : D₁.u ≠ 0 := D₁.u_monic.ne_zero
  have hu₂ : D₂.u ≠ 0 := D₂.u_monic.ne_zero
  have hαorder := orientation_order K D₁ D₂ α hInf
  have hzorder := numerator_order K α D₁.u z hu₁ hzeq
  have hworder := numerator_order K α⁻¹ D₂.u w hu₂ hweq
  have hαinv := inverse_order K α
  have hzplus :
      (-2 : ℤ) ≤ (N13Infinity.coordinateToLaurent K z).order := by
    rw [hzorder, hαorder]
    have hbound := D₁.infinity_bound
    omega
  have hwplus :
      (-2 : ℤ) ≤ (N13Infinity.coordinateToLaurent K w).order := by
    rw [hworder, hαinv, hαorder]
    have hbound := D₂.infinity_bound
    omega
  have hP : D₁.u * D₂.u ≠ 0 := mul_ne_zero hu₁ hu₂
  have hPdeg : (D₁.u * D₂.u).natDegree ≤ 4 := by
    rw [Polynomial.natDegree_mul hu₁ hu₂]
    have hdeg₁ := D₁.deg_u
    have hdeg₂ := D₂.deg_u
    omega
  obtain ⟨hzY, hwY⟩ :=
    N13FactorRigidity.factor_pair_coeffY_eq_zero K z w
      (D₁.u * D₂.u) hP hPdeg hprod hzplus hwplus
  let pz := coeff0 M z
  let pw := coeff0 M w
  have hzpoly : z = xClass M pz := by
    have hzY' : coeffY M z = 0 := by simpa [M] using hzY
    rw [← recompose M z]
    rw [hzY']
    simp [pz]
  have hwpoly : w = xClass M pw := by
    have hwY' : coeffY M w = 0 := by simpa [M] using hwY
    rw [← recompose M w]
    rw [hwY']
    simp [pw]
  have hpoly : pz * pw = D₁.u * D₂.u := by
    apply xClass_injective M
    rw [xClass_mul, ← hzpoly, ← hwpoly, hprod]
  have hu₂pz : D₂.u ∣ pz := by
    have hm :
        pz ∈
          (mumfordIdeal M D₂.u D₂.v).comap (xClassHom M) := by
      change xClass M pz ∈ mumfordIdeal M D₂.u D₂.v
      rw [← hzpoly]
      exact hzmem
    have hbase :
        (mumfordIdeal M D₂.u D₂.v).comap (xClassHom M) =
          Ideal.span ({D₂.u} : Set K[X]) := by
      simpa only [toSemi_u, toSemi_v] using
        mumfordIdeal_comap_base M D₂.toSemi
    rw [hbase, Ideal.mem_span_singleton] at hm
    exact hm
  have hu₁pw : D₁.u ∣ pw := by
    have hm :
        pw ∈
          (mumfordIdeal M D₁.u D₁.v).comap (xClassHom M) := by
      change xClass M pw ∈ mumfordIdeal M D₁.u D₁.v
      rw [← hwpoly]
      exact hwmem
    have hbase :
        (mumfordIdeal M D₁.u D₁.v).comap (xClassHom M) =
          Ideal.span ({D₁.u} : Set K[X]) := by
      simpa only [toSemi_u, toSemi_v] using
        mumfordIdeal_comap_base M D₁.toSemi
    rw [hbase, Ideal.mem_span_singleton] at hm
    exact hm
  obtain ⟨c, hpc⟩ := hu₂pz
  obtain ⟨d, hpd⟩ := hu₁pw
  have hcd : c * d = 1 := by
    apply mul_left_cancel₀ hP
    calc
      (D₁.u * D₂.u) * (c * d) =
          (D₂.u * c) * (D₁.u * d) := by ring
      _ = pz * pw := by rw [← hpc, ← hpd]
      _ = D₁.u * D₂.u := hpoly
      _ = (D₁.u * D₂.u) * 1 := by rw [mul_one]
  have hcunit : IsUnit c :=
    isUnit_iff_exists_inv.mpr ⟨d, hcd⟩
  have hpzfield :
      algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M pz) =
        (α : N13Mumford.FunctionField K) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M D₁.u) := by
    rw [← hzpoly]
    exact hzeq
  have hscale :
      (α : N13Mumford.FunctionField K) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M D₁.u) =
        algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M D₂.u) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M c) := by
    calc
      _ = algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M pz) :=
        hpzfield.symm
      _ = algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M (D₂.u * c)) := by
            rw [hpc]
      _ = _ := by rw [xClass_mul, map_mul]
  have hunitX : xClass M c * xClass M d = 1 := by
    rw [← xClass_mul, hcd, xClass_one]
  have huEq : D₁.u = D₂.u :=
    mumford_u_eq_of_principal_scale M D₁.toSemi D₂.toSemi α
      (xClass M c) (xClass M d) hIdeal hscale hunitX
  have hpc' : pz = D₁.u * c := by
    rw [huEq]
    exact hpc
  have huField :
      algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M D₁.u) ≠ 0 := by
    simpa using
      (IsFractionRing.injective
        (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)).ne
        (xClass_ne_zero M hu₁)
  have hαfield :
      (α : N13Mumford.FunctionField K) =
        algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M c) := by
    apply mul_right_cancel₀ huField
    calc
      (α : N13Mumford.FunctionField K) *
            algebraMap (N13Mumford.CoordinateRing K)
              (N13Mumford.FunctionField K) (xClass M D₁.u) =
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M pz) :=
        hpzfield.symm
      _ = algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K)
            (xClass M (D₁.u * c)) := by rw [hpc']
      _ = algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K)
            (xClass M D₁.u * xClass M c) := by rw [xClass_mul]
      _ = algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M c) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M D₁.u) := by
              rw [map_mul]
              ring
  obtain ⟨r, hrunit, hCr⟩ := Polynomial.isUnit_iff.mp hcunit
  let cr : Kˣ := hrunit.unit
  refine ⟨cr, ?_⟩
  apply Units.ext
  change
    (α : N13Mumford.FunctionField K) =
      algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (algebraMap K (N13Mumford.CoordinateRing K) (cr : K))
  rw [hαfield, ← hCr]
  rfl
end
end MazurProof.N13SmallMumfordRigidity
end

end

theorem solution : type_of% @MazurProof.N13SmallMumfordRigidity.principal_is_constant := @MazurProof.N13SmallMumfordRigidity.principal_is_constant

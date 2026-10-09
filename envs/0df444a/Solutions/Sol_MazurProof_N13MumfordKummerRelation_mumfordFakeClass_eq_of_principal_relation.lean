-- Prove2me | solution 1 for MazurProof.N13MumfordKummerRelation.mumfordFakeClass_eq_of_principal_relation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:10:45.056966+00:00
-- url     : https://prove2.me/submissions/2af68c01-a361-4eec-85fb-d04970ee352f

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_recompose
import Theorems.Thm_MazurProof_SexticMumford_recompose

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

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
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticFunctionConjugation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticFunctionConjugation =====
section
/-!
# Hyperelliptic conjugation on the sextic function field

The affine involution `Y ↦ -Y` extends functorially from the coordinate ring
to the fraction field.  Packaging it as a ring equivalence makes conjugation
of units and fractional ideals available without choosing numerators and
denominators.
-/
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
@[simp] theorem conjugateEquiv_symm (M : Model K) :
    (conjugateEquiv M).symm = conjugateEquiv M := by
  rfl
@[simp] theorem functionConjugateEquiv_algebraMap
    (M : Model K) (z : CoordinateRing M) :
    functionConjugateEquiv M
        (algebraMap (CoordinateRing M) (FunctionField M) z) =
      algebraMap (CoordinateRing M) (FunctionField M) (conjugate M z) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (conjugateEquiv M) z
@[simp] theorem functionConjugateEquiv_symm (M : Model K) :
    (functionConjugateEquiv M).symm = functionConjugateEquiv M := by
  rw [functionConjugateEquiv,
    IsFractionRing.ringEquivOfRingEquiv_symm, conjugateEquiv_symm]
theorem functionConjugate_involutive (M : Model K) :
    Function.Involutive (functionConjugateEquiv M) := by
  intro z
  simpa only [functionConjugateEquiv_symm] using
    (functionConjugateEquiv M).symm_apply_apply z
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdealConjugation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdealConjugation =====
section
/-!
# Conjugation of Mumford ideals

Hyperelliptic conjugation sends `(u, Y-v)` to `(u, Y+v)`.  The following lifts
that elementary generator identity to integral and fractional ideals.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
theorem map_conjugate_mumfordIdeal (M : Model K) (u v : K[X]) :
    Ideal.map (conjugate M) (mumfordIdeal M u v) =
      mumfordIdeal M u (-v) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change conjugate M (xClass M u) ∈ mumfordIdeal M u (-v)
      rw [conjugate_xClass]
      exact xClass_mem_mumfordIdeal M u (-v)
    · change conjugate M (ySubClass M v) ∈ mumfordIdeal M u (-v)
      have htarget : ySubClass M (-v) ∈ mumfordIdeal M u (-v) :=
        ySubClass_mem_mumfordIdeal M u (-v)
      have heq :
          conjugate M (ySubClass M v) = -ySubClass M (-v) := by
        simp [ySubClass]
        ring
      rw [heq]
      exact (mumfordIdeal M u (-v)).neg_mem htarget
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · simpa using Ideal.mem_map_of_mem (conjugate M)
        (xClass_mem_mumfordIdeal M u v)
    · have hsource :
          -ySubClass M v ∈ mumfordIdeal M u v :=
        (mumfordIdeal M u v).neg_mem
          (ySubClass_mem_mumfordIdeal M u v)
      have hmap := Ideal.mem_map_of_mem (conjugate M) hsource
      have heq :
          conjugate M (-ySubClass M v) = ySubClass M (-v) := by
        simp [ySubClass]
        ring
      rw [← heq]
      exact hmap
theorem conjugateFractionalIdealEquiv_coeIdeal
    (M : Model K) (I : Ideal (CoordinateRing M)) :
    conjugateFractionalIdealEquiv M
        (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (Ideal.map (conjugate M) I :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  ext x
  simp only [conjugateFractionalIdealEquiv,
    FractionalIdeal.ringEquivOfRingEquiv_apply,
    FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨conjugate M a, Ideal.mem_map_of_mem (conjugate M) ha, ?_⟩
    change algebraMap (CoordinateRing M) (FunctionField M)
        (conjugate M a) =
      functionConjugateEquiv M
        (algebraMap (CoordinateRing M) (FunctionField M) a)
    exact (functionConjugateEquiv_algebraMap M a).symm
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.mem_map_iff_of_surjective (conjugate M)
      (conjugate_involutive M).surjective] at hb
    obtain ⟨a, ha, hab⟩ := hb
    refine ⟨algebraMap (CoordinateRing M) (FunctionField M) a,
      FractionalIdeal.mem_coeIdeal_of_mem _ ha, ?_⟩
    change functionConjugateEquiv M
        (algebraMap (CoordinateRing M) (FunctionField M) a) =
      algebraMap (CoordinateRing M) (FunctionField M) b
    rw [functionConjugateEquiv_algebraMap, hab]
@[simp] theorem conjugateFractionalIdealEquiv_mumfordIdeal
    (M : Model K) (u v : K[X]) :
    conjugateFractionalIdealEquiv M
        (mumfordIdeal M u v :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (mumfordIdeal M u (-v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  rw [conjugateFractionalIdealEquiv_coeIdeal,
    map_conjugate_mumfordIdeal]
@[simp] theorem conjugateFractionalIdealEquiv_spanSingleton
    (M : Model K) (z : FunctionField M) :
    conjugateFractionalIdealEquiv M
        (FractionalIdeal.spanSingleton (CoordinateRing M)⁰ z) =
      FractionalIdeal.spanSingleton (CoordinateRing M)⁰
        (functionConjugateEquiv M z) := by
  exact FractionalIdeal.ringEquivOfRingEquiv_spanSingleton
    (FunctionField M) (FunctionField M) (conjugateEquiv M) z
@[simp] theorem conjugateInvFrac_principal
    (M : Model K) (z : (FunctionField M)ˣ) :
    conjugateInvFrac M
        (toPrincipalIdeal (CoordinateRing M) (FunctionField M) z) =
      toPrincipalIdeal (CoordinateRing M) (FunctionField M)
        (conjugateFunctionUnit M z) := by
  apply Units.ext
  change conjugateFractionalIdealEquiv M
      ((toPrincipalIdeal (CoordinateRing M) (FunctionField M) z :
        InvFrac M) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
    ((toPrincipalIdeal (CoordinateRing M) (FunctionField M)
      (conjugateFunctionUnit M z) : InvFrac M) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
  rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal,
    conjugateFractionalIdealEquiv_spanSingleton,
    conjugateFunctionUnit_val]
@[simp] theorem conjugateInvFrac_mumfordIdealUnit
    (M : Model K) (D : SemiMumford M) :
    conjugateInvFrac M (mumfordIdealUnit M D) =
      mumfordIdealUnit M (conjugateSemiMumford M D) := by
  apply Units.ext
  change conjugateFractionalIdealEquiv M
      (mumfordIdeal M D.u D.v :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
    (mumfordIdeal M D.u (-D.v) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
  rw [conjugateFractionalIdealEquiv_mumfordIdeal]
theorem conjugate_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (z : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) z =
        mumfordIdealUnit M D₂) :
    mumfordIdealUnit M (conjugateSemiMumford M D₁) *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M)
            (conjugateFunctionUnit M z) =
        mumfordIdealUnit M (conjugateSemiMumford M D₂) := by
  have hmap := congrArg (conjugateInvFrac M) h
  simpa only [map_mul, conjugateInvFrac_mumfordIdealUnit,
    conjugateInvFrac_principal] using hmap
end
end MazurProof.SexticMumford
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

-- ===== FLT.Assumptions.MazurProof.FakeSquareClass =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.FakeSquareClass =====
section
/-!
# The fake square-class target

This file defines
`Lˣ / ((Lˣ)^2 * image(Kˣ))`
for a homomorphism of commutative rings `K →+* L`.

The product of the two subgroups is written as their supremum: `Lˣ` is
commutative, so this is the subgroup generated by squares and rational scalars.
-/
namespace MazurProof.FakeSquareClass
variable {K L : Type*} [CommRing K] [CommRing L]
/-- A scalar is trivial in the fake square-class target. -/
theorem scalar_eq_one (e : K →+* L) (q : Kˣ) :
    ((scalarUnitsMap e q : Lˣ) : Target e) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Subgroup.mem_sup_right
  exact Subgroup.mem_map_of_mem (scalarUnitsMap e)
    (show q ∈ (⊤ : Subgroup Kˣ) from trivial)
/-- A square is trivial in the fake square-class target. -/
theorem square_eq_one (e : K →+* L) (s : Lˣ) :
    ((s ^ 2 : Lˣ) : Target e) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Subgroup.mem_sup_left
  exact Subgroup.mem_square.mpr ⟨s, by simp [pow_two]⟩
/-- Every element of the fake square-class target has exponent two. -/
@[simp] theorem target_sq_eq_one (e : K →+* L) (z : Target e) :
    z ^ 2 = 1 := by
  refine QuotientGroup.induction_on z ?_
  intro s
  exact square_eq_one e s
end MazurProof.FakeSquareClass
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerValue =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerValue =====
section
/-!
# The N13 Mumford fake-Kummer value

Let `θ` be the sextic root.  The branch specialization

`ℚ[X,Y]/(Y²-f(X)) → ℚ(θ),  X ↦ θ,  Y ↦ 0`

turns the quadratic norm of an affine function into a square.  For a
balanced Mumford representative `(u,v,n∞)`, its raw fake-Kummer value is
the unit `u(θ)`, modulo squares and rational scalars.

Irreducibility of the sextic is used only to install the field structure
locally and hence turn the nonzero element `u(θ)` into a unit.  This file
does not yet assert that the value is independent of the chosen Mumford
representative; that is the next principal-ideal relation theorem.
-/
open Polynomial
namespace MazurProof.N13MumfordKummerValue
noncomputable section
open SexticMumford
attribute [local instance] MazurProof.N13MumfordKummerValue.sexticAlgebraField
@[simp] theorem thetaBranch_yClass :
    thetaBranch (yClass M) = 0 := by
  exact AdjoinRoot.lift_root thetaBranch_root
theorem thetaBranch_conjugate
    (z : N13Mumford.CoordinateRing ℚ) :
    thetaBranch (conjugate M z) = thetaBranch z := by
  conv_lhs =>
    rw [← recompose M z]
  conv_rhs =>
    rw [← recompose M z]
  simp
end
end MazurProof.N13MumfordKummerValue
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordFixedUnit =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordFixedUnit =====
section
/-!
# Units fixed by hyperelliptic conjugation

In the affine coordinate ring of a smooth monic sextic, a unit fixed by
hyperelliptic conjugation is a scalar.  This is the structural unit lemma
needed to make the fake Mumford--Kummer value independent of principal
ideal representatives.

The proof uses the rank-two basis `p(X) + q(X)Y`.  Conjugation changes the
sign of `q`, so characteristic zero forces `q = 0`.  Applying the same
basis to the inverse of the unit then shows that `p` is already a unit of
the polynomial ring, hence a nonzero constant.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
theorem conjugate_eq_coeffs (z : CoordinateRing M) :
    conjugate M z =
      xClass M (coeff0 M z) -
        xClass M (coeffY M z) * yClass M := by
  conv_lhs =>
    rw [← recompose M z]
  simp only [map_add, map_mul, conjugate_xClass, conjugate_yClass]
  ring
@[simp] theorem coeffY_conjugate (z : CoordinateRing M) :
    coeffY M (conjugate M z) = -(coeffY M z) := by
  rw [conjugate_eq_coeffs]
  simp
variable [CharZero K]
/-- A coordinate-ring unit fixed by hyperelliptic conjugation is induced
by a unique nonzero scalar of the ground field. -/
theorem fixed_coordinate_unit_is_scalar
    (epsilon : (CoordinateRing M)ˣ)
    (hfix : conjugate M (epsilon : CoordinateRing M) = epsilon) :
    ∃ q : Kˣ,
      epsilon =
        Units.map
          (algebraMap K (CoordinateRing M)).toMonoidHom q := by
  let p : K[X] := coeff0 M (epsilon : CoordinateRing M)
  have hYeq := congrArg (coeffY M) hfix
  rw [coeffY_conjugate] at hYeq
  have hY : coeffY M (epsilon : CoordinateRing M) = 0 :=
    CharZero.neg_eq_self_iff.mp hYeq
  have hepsilon :
      (epsilon : CoordinateRing M) = xClass M p := by
    calc
      (epsilon : CoordinateRing M) =
          xClass M (coeff0 M (epsilon : CoordinateRing M)) +
            xClass M (coeffY M (epsilon : CoordinateRing M)) *
              yClass M :=
        (recompose M (epsilon : CoordinateRing M)).symm
      _ = xClass M p := by simp [p, hY]
  let epsilonInv : CoordinateRing M :=
    (epsilon⁻¹ : (CoordinateRing M)ˣ)
  let r : K[X] := coeff0 M epsilonInv
  have hprod :
      (epsilon : CoordinateRing M) * epsilonInv = 1 := by
    simp [epsilonInv]
  have hp : p ≠ 0 := by
    intro hp0
    exact epsilon.ne_zero (by
      rw [hepsilon, hp0, xClass_zero])
  have hinvY : coeffY M epsilonInv = 0 := by
    have hc := congrArg (coeffY M) hprod
    rw [hepsilon, coeffY_xClass_mul] at hc
    have hone :
        coeffY M (1 : CoordinateRing M) = 0 := by
      rw [← xClass_one M, coeffY_xClass]
    rw [hone] at hc
    exact (mul_eq_zero.mp hc).resolve_left hp
  have hepsilonInv :
      epsilonInv = xClass M r := by
    calc
      epsilonInv =
          xClass M (coeff0 M epsilonInv) +
            xClass M (coeffY M epsilonInv) * yClass M :=
        (recompose M epsilonInv).symm
      _ = xClass M r := by simp [r, hinvY]
  have hpr : p * r = 1 := by
    apply xClass_injective M
    calc
      xClass M (p * r) = xClass M p * xClass M r :=
        xClass_mul M p r
      _ = (epsilon : CoordinateRing M) * epsilonInv := by
        rw [hepsilon, hepsilonInv]
      _ = 1 := hprod
      _ = xClass M 1 := (xClass_one M).symm
  have hpunit : IsUnit p := by
    rw [isUnit_iff_exists]
    exact ⟨r, hpr, by simpa [mul_comm] using hpr⟩
  obtain ⟨a, ha, hCa⟩ := Polynomial.isUnit_iff.mp hpunit
  refine ⟨ha.unit, ?_⟩
  apply Units.ext
  change
    (epsilon : CoordinateRing M) =
      algebraMap K (CoordinateRing M) (ha.unit : K)
  rw [hepsilon, ← hCa]
  rw [IsUnit.unit_spec]
  rfl
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerRelation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerRelation =====
section
/-!
# Principal relations and the N13 Mumford fake-Kummer value

The value `u(θ)` must not depend on a balanced Mumford representative.  The
reason is ideal-theoretic, not a case split on the degree of `u`.

If

`I₁ (α) = I₂`,

then multiplying this relation by its hyperelliptic conjugate gives

`(u₁) (α * ᾱ) = (u₂)`.

The ratio of the two generators is therefore a unit of the affine coordinate
ring.  It is fixed by hyperelliptic conjugation, hence is a nonzero rational
scalar.  Integral numerator and conumerator witnesses then give

`u₁(θ) u₂(θ) = q z(θ)^2`.

Thus the two values have the same class modulo squares and rational scalars.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13MumfordKummerRelation
noncomputable section
open SexticMumford
attribute [local instance] MazurProof.N13MumfordKummerRelation.sexticAlgebraField
theorem exists_fixed_norm_unit
    (D₁ D₂ : N13Mumford.SemiMumford ℚ)
    (α : Fˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal R F α =
        mumfordIdealUnit M D₂) :
    ∃ ε : Rˣ,
      algebraMap R F (ε : R) *
          ((α : F) *
            (conjugateFunctionUnit M α : F) *
            algebraMap R F (xClass M D₁.u)) =
        algebraMap R F (xClass M D₂.u) ∧
      conjugate M (ε : R) = ε := by
  let αbar : Fˣ := conjugateFunctionUnit M α
  have hbar :=
    conjugate_principal_relation M D₁ D₂ α h
  have hnorm :
      (mumfordIdealUnit M D₁ *
          mumfordIdealUnit M (conjugateSemiMumford M D₁)) *
          toPrincipalIdeal R F (α * αbar) =
        mumfordIdealUnit M D₂ *
          mumfordIdealUnit M (conjugateSemiMumford M D₂) := by
    calc
      _ =
          (mumfordIdealUnit M D₁ *
              toPrincipalIdeal R F α) *
            (mumfordIdealUnit M (conjugateSemiMumford M D₁) *
              toPrincipalIdeal R F αbar) := by
                rw [map_mul]
                ac_rfl
      _ = _ := by
        rw [h]
        simpa [αbar] using hbar
  have hfrac := congrArg
    (fun U : InvFrac M =>
      (U : FractionalIdeal R⁰ F)) hnorm
  simp only [Units.val_mul, coe_toPrincipalIdeal,
    coe_mumfordIdealUnit] at hfrac
  simp only [conjugateSemiMumford_u,
    conjugateSemiMumford_v] at hfrac
  rw [mumfordIdeal_mul_conj_fractional M D₁,
    mumfordIdeal_mul_conj_fractional M D₂,
    FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton] at hfrac
  change
    FractionalIdeal.spanSingleton R⁰
        (algebraMap R F (xClass M D₁.u) *
          ((α : F) * (αbar : F))) =
      FractionalIdeal.spanSingleton R⁰
        (algebraMap R F (xClass M D₂.u)) at hfrac
  obtain ⟨e, he⟩ :=
    FractionalIdeal.spanSingleton_eq_spanSingleton.mp hfrac
  rw [Units.smul_def, Algebra.smul_def] at he
  let ε : Rˣ := e
  have heq :
      algebraMap R F (ε : R) *
          ((α : F) * (αbar : F) *
            algebraMap R F (xClass M D₁.u)) =
        algebraMap R F (xClass M D₂.u) := by
    change
      algebraMap R F e *
          ((α : F) * (αbar : F) *
            algebraMap R F (xClass M D₁.u)) =
        algebraMap R F (xClass M D₂.u)
    rw [← he]
    ring
  have hfixedField :
      functionConjugateEquiv M
          ((α : F) * (αbar : F) *
            algebraMap R F (xClass M D₁.u)) =
        (α : F) * (αbar : F) *
          algebraMap R F (xClass M D₁.u) := by
    simp only [map_mul, functionConjugateEquiv_algebraMap,
      conjugate_xClass, αbar, conjugateFunctionUnit_val]
    rw [functionConjugate_involutive]
    ring
  have hconjEq := congrArg (functionConjugateEquiv M) heq
  simp only [map_mul, functionConjugateEquiv_algebraMap,
    conjugate_xClass, hfixedField] at hconjEq
  have hnormNe :
      (α : F) * (αbar : F) *
          algebraMap R F (xClass M D₁.u) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero α.ne_zero αbar.ne_zero)
      (by
        simpa only [map_zero] using
          (IsFractionRing.injective R F).ne
            (xClass_ne_zero M D₁.u_monic.ne_zero))
  have hfix : conjugate M (ε : R) = ε := by
    apply IsFractionRing.injective R F
    apply mul_right_cancel₀ hnormNe
    calc
      algebraMap R F (conjugate M (ε : R)) *
          ((α : F) * (αbar : F) *
            algebraMap R F (xClass M D₁.u)) =
        algebraMap R F (xClass M D₂.u) := hconjEq
      _ =
        algebraMap R F (ε : R) *
          ((α : F) * (αbar : F) *
            algebraMap R F (xClass M D₁.u)) := heq.symm
  exact ⟨ε, heq, hfix⟩
/-- The structural scalar-square relation behind principal invariance.
The witness `z` is the integral numerator of the principal multiplier. -/
theorem exists_scalar_square_product_of_principal_relation
    (D₁ D₂ : N13Mumford.Mumford ℚ)
    (α : Fˣ)
    (h :
      mumfordIdealUnit M D₁.toSemi *
          toPrincipalIdeal R F α =
        mumfordIdealUnit M D₂.toSemi) :
    ∃ q : ℚˣ, ∃ z : R,
      N13MumfordKummerValue.thetaBranch z ≠ 0 ∧
      N13MumfordKummerValue.uTheta D₁ *
          N13MumfordKummerValue.uTheta D₂ =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ) *
          N13MumfordKummerValue.thetaBranch z ^ 2 := by
  obtain ⟨ε, hnorm, hfix⟩ :=
    exists_fixed_norm_unit D₁.toSemi D₂.toSemi α h
  obtain ⟨q, hε⟩ :=
    fixed_coordinate_unit_is_scalar M ε hfix
  obtain ⟨z, w, -, -, hzw, hz, hw⟩ :=
    exists_integral_factor_pair_of_principal_relation
      M D₁.toSemi D₂.toSemi α h
  have hzbarF :
      algebraMap R F (conjugate M z) =
        (conjugateFunctionUnit M α : F) *
          algebraMap R F (xClass M D₁.u) := by
    have hzconj := congrArg (functionConjugateEquiv M) hz
    simpa only [map_mul, functionConjugateEquiv_algebraMap,
      conjugate_xClass, conjugateFunctionUnit_val,
      toSemi_u] using hzconj
  have hnorm' :
      algebraMap R F (ε : R) *
          ((α : F) *
            (conjugateFunctionUnit M α : F) *
            algebraMap R F (xClass M D₁.u)) =
        algebraMap R F (xClass M D₂.u) := by
    simpa only [toSemi_u] using hnorm
  have hwbarF :
      algebraMap R F w =
        algebraMap R F (ε : R) *
          algebraMap R F (conjugate M z) := by
    calc
      algebraMap R F w =
          (↑α⁻¹ : F) *
            algebraMap R F (xClass M D₂.u) := hw
      _ =
          (↑α⁻¹ : F) *
            (algebraMap R F (ε : R) *
              ((α : F) *
                (conjugateFunctionUnit M α : F) *
                algebraMap R F (xClass M D₁.u))) := by
                  rw [hnorm']
      _ =
          algebraMap R F (ε : R) *
            ((conjugateFunctionUnit M α : F) *
              algebraMap R F (xClass M D₁.u)) := by
                rw [Units.val_inv_eq_inv_val]
                field_simp
      _ =
          algebraMap R F (ε : R) *
            algebraMap R F (conjugate M z) := by rw [hzbarF]
  have hwbar :
      w = (ε : R) * conjugate M z := by
    apply IsFractionRing.injective R F
    rw [map_mul]
    exact hwbarF
  have hεtheta :
      N13MumfordKummerValue.thetaBranch (ε : R) =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ) := by
    rw [hε]
    change
      N13MumfordKummerValue.thetaBranch
          (xClass M (C (q : ℚ))) =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ)
    rw [N13MumfordKummerValue.thetaBranch_xClass]
    simp
  have hwtheta :
      N13MumfordKummerValue.thetaBranch w =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ) *
          N13MumfordKummerValue.thetaBranch z := by
    have hθ := congrArg N13MumfordKummerValue.thetaBranch hwbar
    rw [map_mul, N13MumfordKummerValue.thetaBranch_conjugate,
      hεtheta] at hθ
    exact hθ
  have hprod :
      N13MumfordKummerValue.thetaBranch z *
          N13MumfordKummerValue.thetaBranch w =
        N13MumfordKummerValue.uTheta D₁ *
          N13MumfordKummerValue.uTheta D₂ := by
    have hθ := congrArg N13MumfordKummerValue.thetaBranch hzw
    simpa only [map_mul,
      N13MumfordKummerValue.thetaBranch_xClass,
      N13MumfordKummerValue.uTheta_eq_mk,
      toSemi_u] using hθ
  have hztheta :
      N13MumfordKummerValue.thetaBranch z ≠ 0 := by
    intro hzzero
    have hzero :
        N13MumfordKummerValue.uTheta D₁ *
            N13MumfordKummerValue.uTheta D₂ = 0 := by
      rw [← hprod, hzzero, zero_mul]
    exact
      (mul_ne_zero
        (N13MumfordKummerValue.uTheta_ne_zero D₁)
        (N13MumfordKummerValue.uTheta_ne_zero D₂)) hzero
  refine ⟨q, z, hztheta, ?_⟩
  rw [← hprod, hwtheta]
  ring
/-- A principal relation between affine Mumford ideals preserves the raw
fake-Kummer class.  No degree split and no infinity-order hypothesis is
needed. -/
theorem mumfordFakeClass_eq_of_principal_relation
    (D₁ D₂ : N13Mumford.Mumford ℚ)
    (α : Fˣ)
    (h :
      mumfordIdealUnit M D₁.toSemi *
          toPrincipalIdeal R F α =
        mumfordIdealUnit M D₂.toSemi) :
    N13MumfordKummerValue.mumfordFakeClass D₁ =
      N13MumfordKummerValue.mumfordFakeClass D₂ := by
  obtain ⟨q, z, hz, hsq⟩ :=
    exists_scalar_square_product_of_principal_relation D₁ D₂ α h
  let zUnit : N13MumfordKummerValue.Lˣ :=
    Units.mk0 (N13MumfordKummerValue.thetaBranch z) hz
  have hunits :
      N13MumfordKummerValue.uThetaUnit D₁ *
          N13MumfordKummerValue.uThetaUnit D₂ =
        FakeSquareClass.scalarUnitsMap
            (algebraMap ℚ N13MumfordKummerValue.L) q *
          zUnit ^ 2 := by
    apply Units.ext
    change
      N13MumfordKummerValue.uTheta D₁ *
          N13MumfordKummerValue.uTheta D₂ =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ) *
          N13MumfordKummerValue.thetaBranch z ^ 2
    exact hsq
  let c₁ : FakeSquareClass.Target
      (algebraMap ℚ N13MumfordKummerValue.L) :=
    N13MumfordKummerValue.uThetaUnit D₁
  let c₂ : FakeSquareClass.Target
      (algebraMap ℚ N13MumfordKummerValue.L) :=
    N13MumfordKummerValue.uThetaUnit D₂
  have hcprod : c₁ * c₂ = 1 := by
    change
      ((N13MumfordKummerValue.uThetaUnit D₁ *
          N13MumfordKummerValue.uThetaUnit D₂ :
          N13MumfordKummerValue.Lˣ) :
        FakeSquareClass.Target
          (algebraMap ℚ N13MumfordKummerValue.L)) = 1
    rw [hunits]
    change
      ((FakeSquareClass.scalarUnitsMap
          (algebraMap ℚ N13MumfordKummerValue.L) q :
          N13MumfordKummerValue.Lˣ) :
          FakeSquareClass.Target
            (algebraMap ℚ N13MumfordKummerValue.L)) *
        ((zUnit ^ 2 : N13MumfordKummerValue.Lˣ) :
          FakeSquareClass.Target
            (algebraMap ℚ N13MumfordKummerValue.L)) = 1
    rw [FakeSquareClass.scalar_eq_one,
      FakeSquareClass.square_eq_one, one_mul]
  change c₁ = c₂
  calc
    c₁ = c₁ * c₂ ^ 2 := by
      rw [FakeSquareClass.target_sq_eq_one, mul_one]
    _ = (c₁ * c₂) * c₂ := by rw [pow_two, mul_assoc]
    _ = c₂ := by rw [hcprod, one_mul]
end
end MazurProof.N13MumfordKummerRelation
end

end

theorem solution : type_of% @MazurProof.N13MumfordKummerRelation.mumfordFakeClass_eq_of_principal_relation := @MazurProof.N13MumfordKummerRelation.mumfordFakeClass_eq_of_principal_relation

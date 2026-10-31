-- Prove2me | solution 1 for HuangN13.N13ActualPrincipalNorm.norm_of_actual_shape
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:31:06.655697+00:00
-- url     : https://prove2.me/submissions/0d7a3b4b-98f3-4de4-9141-1ea17c7d664a

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore
import Theorems.Thm_MazurProof_N13GoodSexticCoordinateEquiv_sexticYInGood_root
import Theorems.Thm_MazurProof_SexticMumford_recompose

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
@[simp] theorem yClass_sq :
    yClass M ^ 2 = xClass M M.f := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
theorem norm_recompose (p q : K[X]) :
    norm M (xClass M p + xClass M q * yClass M) =
      xClass M (p ^ 2 - q ^ 2 * M.f) := by
  simp only [norm, map_add, map_mul, conjugate_xClass, conjugate_yClass]
  calc
    (xClass M p + xClass M q * yClass M) *
          (xClass M p + xClass M q * -yClass M) =
        xClass M p ^ 2 - xClass M q ^ 2 * yClass M ^ 2 := by ring
    _ = xClass M p ^ 2 - xClass M q ^ 2 * xClass M M.f := by
      rw [yClass_sq]
    _ = xClass M (p ^ 2 - q ^ 2 * M.f) := by
      change
        AdjoinRoot.of (curvePoly M) p ^ 2 -
            AdjoinRoot.of (curvePoly M) q ^ 2 *
              AdjoinRoot.of (curvePoly M) M.f =
          AdjoinRoot.of (curvePoly M) (p ^ 2 - q ^ 2 * M.f)
      simp only [map_sub, map_mul, map_pow]
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
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

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
theorem norm_eq_xClass_coeff (M : Model K) (z : CoordinateRing M) :
    norm M z =
      xClass M
        ((coeff0 M z) ^ 2 - (coeffY M z) ^ 2 * M.f) := by
  conv_lhs =>
    rw [← recompose M z]
  exact norm_recompose M (coeff0 M z) (coeffY M z)
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
@[simp] theorem conjugateEquiv_symm (M : Model K) :
    (conjugateEquiv M).symm = conjugateEquiv M := by
  rfl
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
@[simp] theorem functionConjugateEquiv_algebraMap
    (M : Model K) (z : CoordinateRing M) :
    functionConjugateEquiv M
        (algebraMap (CoordinateRing M) (FunctionField M) z) =
      algebraMap (CoordinateRing M) (FunctionField M) (conjugate M z) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (conjugateEquiv M) z
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
@[simp] theorem functionConjugateEquiv_symm (M : Model K) :
    (functionConjugateEquiv M).symm = functionConjugateEquiv M := by
  rw [functionConjugateEquiv,
    IsFractionRing.ringEquivOfRingEquiv_symm, conjugateEquiv_symm]
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
theorem functionConjugate_involutive (M : Model K) :
    Function.Involutive (functionConjugateEquiv M) := by
  intro z
  simpa only [functionConjugateEquiv_symm] using
    (functionConjugateEquiv M).symm_apply_apply z
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
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
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
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
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
@[simp] theorem conjugateFractionalIdealEquiv_mumfordIdeal
    (M : Model K) (u v : K[X]) :
    conjugateFractionalIdealEquiv M
        (mumfordIdeal M u v :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (mumfordIdeal M u (-v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  rw [conjugateFractionalIdealEquiv_coeIdeal,
    map_conjugate_mumfordIdeal]
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
@[simp] theorem conjugateFractionalIdealEquiv_spanSingleton
    (M : Model K) (z : FunctionField M) :
    conjugateFractionalIdealEquiv M
        (FractionalIdeal.spanSingleton (CoordinateRing M)⁰ z) =
      FractionalIdeal.spanSingleton (CoordinateRing M)⁰
        (functionConjugateEquiv M z) := by
  exact FractionalIdeal.ringEquivOfRingEquiv_spanSingleton
    (FunctionField M) (FunctionField M) (conjugateEquiv M) z
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
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
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
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
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GeneralizedMumfordIntegral
noncomputable section
universe u
variable {R : Type u} [CommRing R]
@[simp] theorem xClass_natCast (n : ℕ) :
    xClass (n : R[X]) =
      (n : CoordinateRing (R := R)) :=
  map_natCast xClassHom n
end
end MazurProof.N13GeneralizedMumfordIntegral
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GeneralizedMumfordIntegral
noncomputable section
universe u
variable {R : Type u} [CommRing R]
@[simp] theorem xClass_add (p q : R[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q
end
end MazurProof.N13GeneralizedMumfordIntegral
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GoodSexticCoordinateEquiv
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
@[simp] theorem toGood_xClass (p : K[X]) :
    toGood (K := K) (SexticMumford.xClass (M (K := K)) p) =
      N13GeneralizedMumfordIntegral.xClass p := by
  change
    toGood (K := K)
        (AdjoinRoot.of
          (SexticMumford.curvePoly (M (K := K))) p) =
      goodXHom (K := K) p
  exact AdjoinRoot.lift_of (MazurProof.N13GoodSexticCoordinateEquiv.sexticYInGood_root (K := K))
end
end MazurProof.N13GoodSexticCoordinateEquiv
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GoodSexticCoordinateEquiv
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
@[simp] theorem toGood_yClass :
    toGood (K := K) (SexticMumford.yClass (M (K := K))) =
      sexticYInGood (K := K) :=
  AdjoinRoot.lift_root (MazurProof.N13GoodSexticCoordinateEquiv.sexticYInGood_root (K := K))
end
end MazurProof.N13GoodSexticCoordinateEquiv
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicAbelChartData
noncomputable section
namespace DiskPair
variable (P : DiskPair)
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem basePair_u :
    basePair.u =
      N13FormalAbelLinearization.uBase := by
  simp [u, basePair, N13FormalAbelLinearization.uBase]
  ring
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
end
end

section
section
set_option autoImplicit false
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
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
@[simp] theorem coeffY_conjugate (z : CoordinateRing M) :
    coeffY M (conjugate M z) = -(coeffY M z) := by
  rw [conjugate_eq_coeffs]
  simp
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
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

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalBranchBalance
noncomputable section
open Polynomial SexticMumford
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K] [CharZero K]
theorem exists_scalar_norm_ratio
    (D₀ D₁ D₂ D₃ : N13Mumford.SemiMumford K) (α : Fˣ)
    (h : mumfordIdealUnit M D₀ * mumfordIdealUnit M D₁ *
        toPrincipalIdeal R F α = mumfordIdealUnit M D₂ * mumfordIdealUnit M D₃) :
    ∃ q : Kˣ,
      N13Infinity.functionConstUnit K q *
          (α * conjugateFunctionUnit M α) *
          xClassFunctionUnit M (D₀.u * D₁.u)
            (mul_ne_zero D₀.u_monic.ne_zero D₁.u_monic.ne_zero) =
        xClassFunctionUnit M (D₂.u * D₃.u)
          (mul_ne_zero D₂.u_monic.ne_zero D₃.u_monic.ne_zero) := by
  let αbar : Fˣ := conjugateFunctionUnit M α
  have hbar := congrArg (conjugateInvFrac M) h
  simp only [map_mul, conjugateInvFrac_mumfordIdealUnit, conjugateInvFrac_principal] at hbar
  have hnorm :
      (mumfordIdealUnit M D₀ * mumfordIdealUnit M (conjugateSemiMumford M D₀)) *
        (mumfordIdealUnit M D₁ * mumfordIdealUnit M (conjugateSemiMumford M D₁)) *
        toPrincipalIdeal R F (α * αbar) =
      (mumfordIdealUnit M D₂ * mumfordIdealUnit M (conjugateSemiMumford M D₂)) *
        (mumfordIdealUnit M D₃ * mumfordIdealUnit M (conjugateSemiMumford M D₃)) := by
    calc
      _ = (mumfordIdealUnit M D₀ * mumfordIdealUnit M D₁ * toPrincipalIdeal R F α) *
          (mumfordIdealUnit M (conjugateSemiMumford M D₀) *
            mumfordIdealUnit M (conjugateSemiMumford M D₁) * toPrincipalIdeal R F αbar) := by
        rw [map_mul]
        ac_rfl
      _ = _ := by
        rw [h]
        dsimp only [αbar]
        rw [hbar]
        ac_rfl
  have hfrac := congrArg (fun U : InvFrac M => U.val) hnorm
  simp only [Units.val_mul, coe_toPrincipalIdeal, coe_mumfordIdealUnit,
    conjugateSemiMumford_u, conjugateSemiMumford_v] at hfrac
  rw [mumfordIdeal_mul_conj_fractional M D₀,
    mumfordIdeal_mul_conj_fractional M D₁,
    mumfordIdeal_mul_conj_fractional M D₂,
    mumfordIdeal_mul_conj_fractional M D₃] at hfrac
  simp only [FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton] at hfrac
  change FractionalIdeal.spanSingleton R⁰
      (algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M D₀.u) * algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M D₁.u) *
        ((α : N13Mumford.FunctionField K) * (αbar : N13Mumford.FunctionField K))) =
    FractionalIdeal.spanSingleton R⁰
      (algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M D₂.u) * algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M D₃.u)) at hfrac
  obtain ⟨ε, he⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hfrac
  rw [Units.smul_def, Algebra.smul_def] at he
  have heq : algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (ε : N13Mumford.CoordinateRing K) *
      ((α : N13Mumford.FunctionField K) * (αbar : N13Mumford.FunctionField K) * algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₀.u * D₁.u))) =
      algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₂.u * D₃.u)) := by
    simp only [xClass_mul, map_mul]
    rw [← he]
    ring
  have hfixed : functionConjugateEquiv M
      ((α : N13Mumford.FunctionField K) * (αbar : N13Mumford.FunctionField K) * algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₀.u * D₁.u))) =
      (α : N13Mumford.FunctionField K) * (αbar : N13Mumford.FunctionField K) * algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₀.u * D₁.u)) := by
    simp only [map_mul, functionConjugateEquiv_algebraMap,
      conjugate_xClass, αbar, conjugateFunctionUnit_val]
    rw [functionConjugate_involutive]
    ring
  have hconj := congrArg (functionConjugateEquiv M) heq
  simp only [map_mul, functionConjugateEquiv_algebraMap, conjugate_xClass, hfixed] at hconj
  have hne : (α : N13Mumford.FunctionField K) * (αbar : N13Mumford.FunctionField K) *
      algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₀.u * D₁.u)) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero α.ne_zero αbar.ne_zero)
    simpa only [map_zero] using (IsFractionRing.injective (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K)).ne
      (xClass_ne_zero M (mul_ne_zero D₀.u_monic.ne_zero D₁.u_monic.ne_zero))
  have hε : conjugate M (ε : N13Mumford.CoordinateRing K) = ε := by
    apply IsFractionRing.injective (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K)
    apply mul_right_cancel₀ hne
    exact hconj.trans heq.symm
  obtain ⟨q, hq⟩ := fixed_coordinate_unit_is_scalar M ε hε
  refine ⟨q, ?_⟩
  apply Units.ext
  change algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K)
      (Units.map (algebraMap K (N13Mumford.CoordinateRing K)).toMonoidHom q : N13Mumford.CoordinateRing K) *
        ((α : N13Mumford.FunctionField K) * (conjugateFunctionUnit M α : N13Mumford.FunctionField K)) *
        algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₀.u * D₁.u)) =
      algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₂.u * D₃.u))
  rw [← hq]
  simpa only [mul_assoc, αbar] using heq
end
end MazurProof.N13PrincipalBranchBalance
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GoodCenteredNumerator
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT
theorem toGood_recompose (n : R) :
    toGood n = gx (goodP n) + gx (goodQ n) * gy := by
  conv_lhs => rw [← recompose M n]
  rw [map_add, map_mul,
    N13GoodSexticCoordinateEquiv.toGood_xClass,
    N13GoodSexticCoordinateEquiv.toGood_xClass,
    N13GoodSexticCoordinateEquiv.toGood_yClass]
  simp only [goodP, goodQ, N13GoodSexticCoordinateEquiv.sexticYInGood,
    N13GoodSexticCoordinateEquiv.goodXHom_apply,
    N13GeneralizedMumfordIntegral.xClass_add,
    N13GeneralizedMumfordIntegral.xClass_mul,
    N13GeneralizedMumfordIntegral.xClass_natCast]
  have h2 : N13GeneralizedMumfordIntegral.xClass (2 : K[X]) = 2 := by
    have := N13GeneralizedMumfordIntegral.xClass_natCast (R := K) 2
    exact_mod_cast this
  rw [h2]
  ring
end
end MazurProof.N13GoodCenteredNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ActualPrincipalNorm
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT
theorem norm_polynomial_of_principal
    (D₀ D₁ D₂ D₃ : N13Mumford.SemiMumford K) (α : Fˣ) (n : R)
    (h : mumfordIdealUnit M D₀ * mumfordIdealUnit M D₁ * toPrincipalIdeal R F α =
      mumfordIdealUnit M D₂ * mumfordIdealUnit M D₃)
    (hn : algebraMap R F n = (α : F) * algebraMap R F (xClass M (D₀.u * D₁.u))) :
    ∃ k : Kˣ,
      (coeff0 M n) ^ 2 - (coeffY M n) ^ 2 * M.f =
        _root_.Polynomial.C (k : K) * (D₀.u * D₁.u) * (D₂.u * D₃.u) := by
  obtain ⟨q, hq⟩ := N13PrincipalBranchBalance.exists_scalar_norm_ratio D₀ D₁ D₂ D₃ α h
  let a : F := (N13Infinity.functionConstUnit K q : F)
  let d : F := (N13Infinity.functionConstUnit K q⁻¹ : F)
  let x : F := algebraMap R F (xClass M (D₀.u * D₁.u))
  let y : F := algebraMap R F (xClass M (D₂.u * D₃.u))
  let αbar : F := (conjugateFunctionUnit M α : F)
  have hqf : a * ((α : F) * αbar) * x = y :=
    congrArg (fun u : Fˣ => (u : F)) hq
  have hi : d * a = 1 := by
    change (N13Infinity.functionConstUnit K q⁻¹ : F) *
      (N13Infinity.functionConstUnit K q : F) = 1
    simp [N13Infinity.functionConstUnit, N13Infinity.coordinateConstUnit, ← map_mul]
  have hnbar := congrArg (functionConjugateEquiv M) hn
  simp only [map_mul, functionConjugateEquiv_algebraMap, conjugate_xClass] at hnbar
  have hnorm : algebraMap R F (SexticMumford.norm M n) = (α : F) * αbar * x ^ 2 := by
    rw [SexticMumford.norm, map_mul, hn, hnbar]
    change ((α : F) * x) * (αbar * x) = _
    ring
  have hratio : a * algebraMap R F (SexticMumford.norm M n) = x * y := by
    rw [hnorm]
    calc
      a * ((α : F) * αbar * x ^ 2) = x * (a * ((α : F) * αbar) * x) := by ring
      _ = x * y := by rw [hqf]
  refine ⟨q⁻¹, ?_⟩
  apply xClass_injective M
  rw [← norm_eq_xClass_coeff]
  apply IsFractionRing.injective R F
  calc
    algebraMap R F (SexticMumford.norm M n) = d * (a * algebraMap R F (SexticMumford.norm M n)) := by
      rw [← mul_assoc, hi, one_mul]
    _ = d * (x * y) := by rw [hratio]
    _ = algebraMap R F (xClass M (_root_.Polynomial.C (↑(q⁻¹) : K) * (D₀.u * D₁.u) * (D₂.u * D₃.u))) := by
      rw [xClass_mul, xClass_mul, map_mul, map_mul]
      change algebraMap R F (algebraMap K R (↑(q⁻¹) : K)) * (x * y) =
        (algebraMap R F (algebraMap K R (↑(q⁻¹) : K)) * x) * y
      ring
end
end MazurProof.N13ActualPrincipalNorm
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ActualPrincipalNorm
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT
theorem good_norm_eq_sextic_norm (n : R) :
    goodP n ^ 2 - goodP n * goodQ n * N13GeneralizedMumfordIntegral.hPoly -
      goodQ n ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly =
        (coeff0 M n) ^ 2 - (coeffY M n) ^ 2 * M.f := by
  rw [show M.f = N13Mumford.f K from rfl,
    N13GoodSexticCoordinateEquiv.sextic_eq_h_sq_add_four_rhs (K := K)]
  unfold goodP goodQ
  ring
end
end MazurProof.N13ActualPrincipalNorm
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ActualPrincipalNorm
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT
theorem shape_coefficients (n : R) (A b : K[X])
    (hshape : toGood n = gx ((X ^ 2 + X) * A) + gx b * gy) :
    goodP n = (X ^ 2 + X) * A ∧ goodQ n = b := by
  have he := (toGood_recompose n).symm.trans hshape
  constructor
  · have h := congrArg N13GeneralizedMumfordIntegral.coeff0 he
    simpa only [map_add, N13GeneralizedMumfordIntegral.coeff0_xClass,
      N13GeneralizedMumfordIntegral.coeff0_xClass_mul_yClass, add_zero] using h
  · have h := congrArg N13GeneralizedMumfordIntegral.coeffY he
    simpa only [map_add, N13GeneralizedMumfordIntegral.coeffY_xClass,
      N13GeneralizedMumfordIntegral.coeffY_xClass_mul_yClass, zero_add] using h
end
end MazurProof.N13ActualPrincipalNorm
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ActualPrincipalNorm
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13ActualPrincipalNorm.instFactPrimeOfNatNat_fLT
theorem norm_of_actual_shape (P Q : DiskPair) (α : Fˣ) (n : R) (A b : K[X])
    (h : mumfordIdealUnit M P.mumford.toSemi * mumfordIdealUnit M P.mumford.toSemi *
      toPrincipalIdeal R F α = mumfordIdealUnit M Q.mumford.toSemi *
        mumfordIdealUnit M B.mumford.toSemi)
    (hn : algebraMap R F n = (α : F) * algebraMap R F (xClass M (P.mumford.u ^ 2)))
    (hshape : toGood n = gx ((X ^ 2 + X) * A) + gx b * gy) :
    ∃ k : Kˣ,
      ((X ^ 2 + X) * A) ^ 2 - ((X ^ 2 + X) * A) * b *
          N13GeneralizedMumfordIntegral.hPoly - b ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly =
        _root_.Polynomial.C (k : K) * (N13TwoAdicMumfordTransport.mapPoly P.u) ^ 2 *
          (X ^ 2 + X) * N13TwoAdicMumfordTransport.mapPoly Q.u := by
  obtain ⟨k, hk⟩ := norm_polynomial_of_principal P.mumford.toSemi P.mumford.toSemi
    Q.mumford.toSemi B.mumford.toSemi α n h (by rw [← pow_two]; exact hn)
  obtain ⟨hp, hq⟩ := shape_coefficients n A b hshape
  have hB : B.mumford.u = (X ^ 2 + X : K[X]) := by
    simp [N13TwoAdicAbelChartPic.DiskPair.mumford_u,
      N13TwoAdicMumfordTransport.mapPoly, N13FormalAbelLinearization.uBase]
  refine ⟨k, ?_⟩
  simp only [← hp, ← hq]
  rw [good_norm_eq_sextic_norm, hk]
  change _root_.Polynomial.C (k : K) * (P.mumford.u * P.mumford.u) * (Q.mumford.u * B.mumford.u) = _
  simp only [hB, N13TwoAdicAbelChartPic.DiskPair.mumford_u]
  ring
end
end MazurProof.N13ActualPrincipalNorm
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13ActualPrincipalNorm.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution (P Q : MazurProof.N13CenteredPrincipalNumerator.DiskPair) (α : MazurProof.N13CenteredPrincipalNumerator.Fˣ) (n : MazurProof.N13CenteredPrincipalNumerator.R) (A b : MazurProof.N13CenteredPrincipalNumerator.K[X])
    (h : MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M P.mumford.toSemi * MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M P.mumford.toSemi *
      toPrincipalIdeal MazurProof.N13CenteredPrincipalNumerator.R MazurProof.N13CenteredPrincipalNumerator.F α = MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M Q.mumford.toSemi *
        MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M MazurProof.N13CenteredPrincipalNumerator.B.mumford.toSemi)
    (hn : algebraMap MazurProof.N13CenteredPrincipalNumerator.R MazurProof.N13CenteredPrincipalNumerator.F n = (α : MazurProof.N13CenteredPrincipalNumerator.F) * algebraMap MazurProof.N13CenteredPrincipalNumerator.R MazurProof.N13CenteredPrincipalNumerator.F (MazurProof.SexticMumford.xClass MazurProof.N13CenteredPrincipalNumerator.M (P.mumford.u ^ 2)))
    (hshape : MazurProof.N13GoodCenteredNumerator.toGood n = MazurProof.N13GoodCenteredNumerator.gx ((X ^ 2 + X) * A) + MazurProof.N13GoodCenteredNumerator.gx b * MazurProof.N13GoodCenteredNumerator.gy) :
    ∃ k : MazurProof.N13CenteredPrincipalNumerator.Kˣ,
      ((X ^ 2 + X) * A) ^ 2 - ((X ^ 2 + X) * A) * b *
          MazurProof.N13GeneralizedMumfordIntegral.hPoly - b ^ 2 * MazurProof.N13GeneralizedMumfordIntegral.rhsPoly =
        C (k : MazurProof.N13CenteredPrincipalNumerator.K) * (MazurProof.N13TwoAdicMumfordTransport.mapPoly P.u) ^ 2 *
          (X ^ 2 + X) * MazurProof.N13TwoAdicMumfordTransport.mapPoly Q.u := by
  exact MazurProof.N13ActualPrincipalNorm.norm_of_actual_shape P Q α n A b h hn hshape

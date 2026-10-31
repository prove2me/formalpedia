-- Prove2me | solution 1 for HuangN13.N13CenteredPrincipalNumerator.multiplier_of_centered_double
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:31:03.314675+00:00
-- url     : https://prove2.me/submissions/ebceca9d-0e43-4208-9a26-d8f467b6f1a9

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore
import Theorems.Thm_MazurProof_SexticMumford_recompose

set_option autoImplicit false

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
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem coordinateToLaurent_scalar (c : K) :
    coordinateToLaurent K (algebraMap K (N13Mumford.CoordinateRing K) c) =
      algebraMap K (LaurentSeries K) c := by
  change coordinateToLaurent K
    (SexticMumford.xClass (N13Mumford.model K) (_root_.Polynomial.C c)) = _
  rw [coordinateToLaurent_xClass]
  simp
end
end MazurProof.N13Infinity
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem functionFieldToLaurent_functionConstUnit (c : Kˣ) :
    functionFieldToLaurent K (functionConstUnit K c :
      N13Mumford.FunctionField K) =
      algebraMap K (LaurentSeries K) (c : K) := by
  change functionFieldToLaurent K
      (algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (algebraMap K (N13Mumford.CoordinateRing K) (c : K))) = _
  rw [functionFieldToLaurent_algebraMap, coordinateToLaurent_scalar]
end
end MazurProof.N13Infinity
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem ordPlus_functionConstUnit (c : Kˣ) :
    (positiveInfinityOrder K).ordPlus (functionConstUnit K c) = 1 := by
  change Multiplicative.ofAdd
      ((functionFieldToLaurent K
        (functionConstUnit K c : N13Mumford.FunctionField K)).order) = 1
  rw [functionFieldToLaurent_functionConstUnit]
  simp [HahnSeries.algebraMap_apply', HahnSeries.order_single c.ne_zero]
end
end MazurProof.N13Infinity
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13InfinityMinus
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem functionFieldToLaurentMinus_algebraMap
    (z : N13Mumford.CoordinateRing K) :
    functionFieldToLaurentMinus K
        (algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) z) =
      coordinateToLaurentMinus K z := by
  exact IsFractionRing.lift_algebraMap
    (coordinateToLaurentMinus_injective K) z
end
end MazurProof.N13InfinityMinus
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13BranchNorm
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem coordinateToLaurent_yClass :
    N13Infinity.coordinateToLaurent K
      (SexticMumford.yClass (N13Mumford.model K)) =
      N13Infinity.ySeries K := by
  change N13Infinity.algebraicToLaurent K
    (N13Infinity.coordinateToAlgebraic K
      (AdjoinRoot.mk
        (SexticMumford.curvePoly (N13Mumford.model K)) X)) = _
  rw [N13Infinity.coordinateToAlgebraic_mk]
  simp only [Polynomial.map_X]
  exact AdjoinRoot.lift_root
    (N13Infinity.curvePolyRat_eval_ySeries K)
end
end MazurProof.N13BranchNorm
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
open scoped LaurentSeries
namespace MazurProof.N13FunctionConjugation
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem coordinateToLaurent_conjugate
    (z : N13Mumford.CoordinateRing K) :
    N13Infinity.coordinateToLaurent K
        (SexticMumford.conjugate (N13Mumford.model K) z) =
      N13InfinityMinus.coordinateToLaurentMinus K z := by
  conv_lhs =>
    rw [← SexticMumford.recompose (N13Mumford.model K) z]
  conv_rhs =>
    rw [← SexticMumford.recompose (N13Mumford.model K) z]
  simp only [map_add, map_mul, map_neg, SexticMumford.conjugate_xClass,
    SexticMumford.conjugate_yClass,
    N13Infinity.coordinateToLaurent_xClass,
    N13BranchNorm.coordinateToLaurent_yClass,
    N13InfinityMinus.coordinateToLaurentMinus_xClass,
    N13InfinityMinus.coordinateToLaurentMinus_yClass,
    N13InfinityMinus.ySeriesMinus_eq_neg]
end
end MazurProof.N13FunctionConjugation
end
end

section
section
set_option autoImplicit false
open scoped LaurentSeries
namespace MazurProof.N13FunctionConjugation
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem functionFieldToLaurent_conjugate
    (z : N13Mumford.FunctionField K) :
    N13Infinity.functionFieldToLaurent K
        (SexticMumford.functionConjugateEquiv
          (N13Mumford.model K) z) =
      N13InfinityMinus.functionFieldToLaurentMinus K z := by
  let lhs : N13Mumford.FunctionField K →+* LaurentSeries K :=
    (N13Infinity.functionFieldToLaurent K).comp
      (SexticMumford.functionConjugateEquiv
        (N13Mumford.model K)).toRingHom
  have hhom :
      lhs = N13InfinityMinus.functionFieldToLaurentMinus K := by
    apply IsFractionRing.ringHom_ext
      (A := N13Mumford.CoordinateRing K)
    intro w
    change N13Infinity.functionFieldToLaurent K
        (SexticMumford.functionConjugateEquiv
          (N13Mumford.model K)
          (algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) w)) =
      N13InfinityMinus.functionFieldToLaurentMinus K
        (algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) w)
    rw [SexticMumford.functionConjugateEquiv_algebraMap,
      N13Infinity.functionFieldToLaurent_algebraMap,
      N13InfinityMinus.functionFieldToLaurentMinus_algebraMap,
      coordinateToLaurent_conjugate]
  change lhs z = _
  rw [hhom]
end
end MazurProof.N13FunctionConjugation
end
end

section
section
set_option autoImplicit false
open scoped LaurentSeries
namespace MazurProof.N13FunctionConjugation
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem positive_order_conjugate_eq_negative
    (z : (N13Mumford.FunctionField K)ˣ) :
    (N13Infinity.positiveInfinityOrder K).ordPlus
        (SexticMumford.conjugateFunctionUnit
          (N13Mumford.model K) z) =
      (N13InfinityMinus.negativeInfinityOrder K).ordPlus z := by
  change Multiplicative.ofAdd
      ((N13Infinity.functionFieldToLaurent K
        (SexticMumford.functionConjugateEquiv
          (N13Mumford.model K)
          (z : N13Mumford.FunctionField K))).order) =
    Multiplicative.ofAdd
      ((N13InfinityMinus.functionFieldToLaurentMinus K
        (z : N13Mumford.FunctionField K)).order)
  rw [functionFieldToLaurent_conjugate]
end
end MazurProof.N13FunctionConjugation
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
namespace MazurProof.N13PrincipalBranchBalance
noncomputable section
open Polynomial SexticMumford
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K] [CharZero K]
/-- Exact degree balance for the two infinity orders of the actual common
principal multiplier between two tensor products of graph ideals. -/
theorem principal_branch_orders_sum
    (D₀ D₁ D₂ D₃ : N13Mumford.SemiMumford K) (α : Fˣ)
    (h : mumfordIdealUnit M D₀ * mumfordIdealUnit M D₁ *
        toPrincipalIdeal R F α = mumfordIdealUnit M D₂ * mumfordIdealUnit M D₃) :
    Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus α) +
        Multiplicative.toAdd ((N13InfinityMinus.negativeInfinityOrder K).ordPlus α) =
      (D₀.u.natDegree : ℤ) + D₁.u.natDegree - D₂.u.natDegree - D₃.u.natDegree := by
  obtain ⟨q, hq⟩ := exists_scalar_norm_ratio D₀ D₁ D₂ D₃ α h
  have ho := congrArg
    (fun z : Fˣ => Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus z)) hq
  simp only [map_mul, toAdd_mul, N13Infinity.ordPlus_functionConstUnit,
    toAdd_one, zero_add,
    N13FunctionConjugation.positive_order_conjugate_eq_negative,
    N13MumfordInfinityBalance.ordPlus_xClassFunctionUnit] at ho
  rw [Polynomial.natDegree_mul D₀.u_monic.ne_zero D₁.u_monic.ne_zero,
    Polynomial.natDegree_mul D₂.u_monic.ne_zero D₃.u_monic.ne_zero,
    Nat.cast_add, Nat.cast_add] at ho
  omega
end
end MazurProof.N13PrincipalBranchBalance
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredPrincipalNumerator
noncomputable section
open SexticMumford
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT
theorem multiplier_of_centered_double (P Q : DiskPair)
    (hc : N13TwoAdicAbelChartPic.DiskPair.centeredPic Q =
      2 • N13TwoAdicAbelChartPic.DiskPair.centeredPic P) :
    ∃ α : Fˣ,
      mumfordIdealUnit M P.mumford.toSemi * mumfordIdealUnit M P.mumford.toSemi *
        toPrincipalIdeal R F α = mumfordIdealUnit M Q.mumford.toSemi *
          mumfordIdealUnit M B.mumford.toSemi ∧
      Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus α) = 0 ∧
      Multiplicative.toAdd ((N13InfinityMinus.negativeInfinityOrder K).ordPlus α) = 0 := by
  have hs : N13TwoAdicAbelChartPic.DiskPair.pic P +
      N13TwoAdicAbelChartPic.DiskPair.pic P =
    N13TwoAdicAbelChartPic.DiskPair.pic Q + N13TwoAdicAbelChartPic.DiskPair.pic B := by
    calc
      _ = 2 • N13TwoAdicAbelChartPic.DiskPair.centeredPic P +
          2 • N13TwoAdicAbelChartPic.DiskPair.pic B := by
        simp only [N13TwoAdicAbelChartPic.DiskPair.centeredPic, two_nsmul]
        abel
      _ = N13TwoAdicAbelChartPic.DiskPair.centeredPic Q +
          2 • N13TwoAdicAbelChartPic.DiskPair.pic B := by rw [← hc]
      _ = _ := by
        simp only [N13TwoAdicAbelChartPic.DiskPair.centeredPic, two_nsmul]
        abel
  let q := QuotientGroup.mk'
    (principalOriented M (N13Infinity.positiveInfinityOrder K)).range
  have hq : q (mumfordRaw M P.mumford * mumfordRaw M P.mumford) =
      q (mumfordRaw M Q.mumford * mumfordRaw M B.mumford) := by
    change q (mumfordRaw M P.mumford) * q (mumfordRaw M P.mumford) =
      q (mumfordRaw M Q.mumford) * q (mumfordRaw M B.mumford) at hs
    simpa only [map_mul] using hs
  change QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _ at hq
  rw [QuotientGroup.mk'_eq_mk'] at hq
  obtain ⟨a, ha, he⟩ := hq
  obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp ha
  have hp := congrArg Prod.fst he
  have hplus : Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus α) = 0 := by
    have hi := congrArg (fun z : OrientedFrac M => Multiplicative.toAdd z.2) he
    change ((-1 : ℤ) + -1) +
      Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus α) = -1 + -1 at hi
    omega
  refine ⟨α, hp, hplus, ?_⟩
  have hsum := N13PrincipalBranchBalance.principal_branch_orders_sum
    P.mumford.toSemi P.mumford.toSemi Q.mumford.toSemi B.mumford.toSemi α hp
  have hd (D : DiskPair) : D.mumford.toSemi.u.natDegree = 2 :=
    N13TwoAdicAbelChartPic.DiskPair.sexticSemi_u_natDegree D
  rw [hplus, hd P, hd Q, hd B] at hsum
  norm_num at hsum
  exact hsum
end
end MazurProof.N13CenteredPrincipalNumerator
end
end


set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
theorem solution (P Q : MazurProof.N13CenteredPrincipalNumerator.DiskPair)
    (hc : MazurProof.N13TwoAdicAbelChartPic.DiskPair.centeredPic Q =
      2 • MazurProof.N13TwoAdicAbelChartPic.DiskPair.centeredPic P) :
    ∃ α : MazurProof.N13CenteredPrincipalNumerator.Fˣ,
      MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M P.mumford.toSemi * MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M P.mumford.toSemi *
        toPrincipalIdeal MazurProof.N13CenteredPrincipalNumerator.R MazurProof.N13CenteredPrincipalNumerator.F α = MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M Q.mumford.toSemi *
          MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M MazurProof.N13CenteredPrincipalNumerator.B.mumford.toSemi ∧
      Multiplicative.toAdd ((MazurProof.N13Infinity.positiveInfinityOrder MazurProof.N13CenteredPrincipalNumerator.K).ordPlus α) = 0 ∧
      Multiplicative.toAdd ((MazurProof.N13InfinityMinus.negativeInfinityOrder MazurProof.N13CenteredPrincipalNumerator.K).ordPlus α) = 0 := by
  exact MazurProof.N13CenteredPrincipalNumerator.multiplier_of_centered_double P Q hc

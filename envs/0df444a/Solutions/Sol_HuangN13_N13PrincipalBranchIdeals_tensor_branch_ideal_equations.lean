-- Prove2me | solution 1 for HuangN13.N13PrincipalBranchIdeals.tensor_branch_ideal_equations
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:44:04.892958+00:00
-- url     : https://prove2.me/submissions/02cad72e-b65a-4126-ae66-92c8e7682d1f

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_OverlapBranchMapsCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Theorems.Thm_HuangN13_N13OverlapBranchCompatibility_branch_cross_relations
import Theorems.Thm_HuangN13_N13OverlapBranchCompatibility_overlap_maps_injective
import Theorems.Thm_MazurProof_N13FormalInfinityChart_infinityCurve_relation
import Theorems.Thm_MazurProof_N13FormalInfinityChart_recompose
import Theorems.Thm_MazurProof_N13IntegralCurveProperties_infinity_tClass_mem_nonZeroDivisors
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
    (SexticMumford.xClass (N13Mumford.model K) (C c)) = _
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
namespace MazurProof.N13EffectiveInfinityRepair
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open SexticMumford N13MumfordInfinityBalance
open Polynomial
theorem positiveMultiplicity_cast
    (E : N13Mumford.SemiMumford K) (h : EffectiveChamber E) :
    (positiveMultiplicity E : ℤ) = E.nInf + 1 := by
  apply Int.toNat_of_nonneg
  have := h.2.1
  omega
end
end MazurProof.N13EffectiveInfinityRepair
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveInfinityRepair
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open SexticMumford N13MumfordInfinityBalance
open Polynomial
theorem negativeMultiplicity_cast
    (E : N13Mumford.SemiMumford K) (h : EffectiveChamber E) :
    (negativeMultiplicity E : ℤ) = 1 - (E.u.natDegree : ℤ) - E.nInf := by
  apply Int.toNat_of_nonneg
  have := h.2.2
  omega
end
end MazurProof.N13EffectiveInfinityRepair
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
open Polynomial
namespace MazurProof.N13FormalInfinityChart
noncomputable section
open HahnSeries
open scoped PowerSeries LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToFormalCurve_vClass :
    infinityToFormalCurve vClass =
      N13FormalCurveOverlap.vClass := by
  exact AdjoinRoot.lift_root infinityCurve_relation
end
end MazurProof.N13FormalInfinityChart
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open CategoryTheory
open Polynomial
open Set Topology
namespace MazurProof.N13IntegralCurveProperties
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinity_powers_le_nonZeroDivisors :
    Submonoid.powers N13IntegralInfinityChart.tClass ≤
      nonZeroDivisors InfinityCurve :=
  Submonoid.powers_le.mpr
    infinity_tClass_mem_nonZeroDivisors
end
end MazurProof.N13IntegralCurveProperties
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open CategoryTheory
open Polynomial
open Set Topology
namespace MazurProof.N13IntegralCurveProperties
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinity_to_overlap_injective :
    Function.Injective
      (algebraMap InfinityCurve InfinityOverlap) :=
  IsLocalization.injective InfinityOverlap
    infinity_powers_le_nonZeroDivisors
end
end MazurProof.N13IntegralCurveProperties
end
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchZero_of
    (f : Power) :
    evalBranchZero
        (AdjoinRoot.of
          N13FormalInfinityChart.infinityCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchZero
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchOne_of
    (f : Power) :
    evalBranchOne
        (AdjoinRoot.of
          N13FormalInfinityChart.infinityCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchOne
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchZero_vClass :
    evalBranchZero N13FormalInfinityChart.vClass =
      branchZero := by
  exact AdjoinRoot.lift_root eval₂_branchZero
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchOne_vClass :
    evalBranchOne N13FormalInfinityChart.vClass =
      branchOne := by
  exact AdjoinRoot.lift_root eval₂_branchOne
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Simultaneous evaluation on the two disjoint Hensel branches. -/
def branchEval : InfinityCurve →+* Power × Power :=
  evalBranchZero.prod evalBranchOne
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchEval_eq_coeff
    (z : InfinityCurve) :
    branchEval z =
      (N13FormalInfinityChart.coeff0 z +
          N13FormalInfinityChart.coeffV z * branchZero,
        N13FormalInfinityChart.coeff0 z +
          N13FormalInfinityChart.coeffV z * branchOne) := by
  calc
    branchEval z =
        branchEval
          (algebraMap Power InfinityCurve
              (N13FormalInfinityChart.coeff0 z) +
            algebraMap Power InfinityCurve
                (N13FormalInfinityChart.coeffV z) *
              N13FormalInfinityChart.vClass) := by
          exact congrArg branchEval
            (N13FormalInfinityChart.recompose z).symm
    _ = _ := by simp [branchEval]
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchZeroLaurent_of
    (f : Laurent) :
    evalBranchZeroLaurent
        (AdjoinRoot.of
          N13FormalCurveOverlap.formalCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchZeroLaurent
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchOneLaurent_of
    (f : Laurent) :
    evalBranchOneLaurent
        (AdjoinRoot.of
          N13FormalCurveOverlap.formalCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchOneLaurent
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchZeroLaurent_vClass :
    evalBranchZeroLaurent N13FormalCurveOverlap.vClass =
      branchZeroLaurent := by
  exact AdjoinRoot.lift_root eval₂_branchZeroLaurent
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchOneLaurent_vClass :
    evalBranchOneLaurent N13FormalCurveOverlap.vClass =
      branchOneLaurent := by
  exact AdjoinRoot.lift_root eval₂_branchOneLaurent
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToFormalCurve_adjoinRootOf
    (f : Power) :
    N13FormalInfinityChart.infinityToFormalCurve
        (AdjoinRoot.of
          N13FormalInfinityChart.infinityCurvePoly f) =
      AdjoinRoot.of N13FormalCurveOverlap.formalCurvePoly
        (N13FormalInfinityChart.includePowerRing f) := by
  exact N13FormalInfinityChart.infinityToFormalCurve_of f
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem formalBranchEval_infinityToFormalCurve
    (z : InfinityCurve) :
    formalBranchEval
        (N13FormalInfinityChart.infinityToFormalCurve z) =
      includePowerBranches
        (N13FormalInfinitySplit.branchEval z) := by
  calc
    formalBranchEval
        (N13FormalInfinityChart.infinityToFormalCurve z) =
      formalBranchEval
        (N13FormalInfinityChart.infinityToFormalCurve
          (algebraMap Power InfinityCurve
              (N13FormalInfinityChart.coeff0 z) +
            algebraMap Power InfinityCurve
                (N13FormalInfinityChart.coeffV z) *
              N13FormalInfinityChart.vClass)) := by
        exact congrArg
          (fun w =>
            formalBranchEval
              (N13FormalInfinityChart.infinityToFormalCurve w))
          (N13FormalInfinityChart.recompose z).symm
    _ =
      (N13FormalInfinityChart.includePowerRing
          (N13FormalInfinityChart.coeff0 z) +
        N13FormalInfinityChart.includePowerRing
            (N13FormalInfinityChart.coeffV z) *
          branchZeroLaurent,
       N13FormalInfinityChart.includePowerRing
          (N13FormalInfinityChart.coeff0 z) +
        N13FormalInfinityChart.includePowerRing
            (N13FormalInfinityChart.coeffV z) *
          branchOneLaurent) := by
        simp [formalBranchEval,
          N13FormalInfinityChart.infinityToFormalCurve_vClass]
    _ =
      includePowerBranches
        (N13FormalInfinitySplit.branchEval z) := by
      rw [N13FormalInfinitySplit.branchEval_eq_coeff]
      simp [includePowerBranches, branchZeroLaurent,
        branchOneLaurent]
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicInfinityCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Extension commutes with the inclusion of power series into Laurent
series. -/
theorem laurentMap_includePower
    (f : IntegralPower) :
    laurentMap
        (N13FormalInfinityChart.includePowerRing f) =
      (HahnSeries.ofPowerSeries ℤ Q₂) (powerMap f) := by
  ext n
  rw [laurentMap_coeff]
  by_cases hn : n < 0
  · simp [N13FormalInfinityChart.includePowerRing,
      PowerSeries.coeff_coe, hn]
  · simp [N13FormalInfinityChart.includePowerRing,
      PowerSeries.coeff_coe, hn]
end
end MazurProof.N13TwoAdicInfinityCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem infinity_tClass_isUnit :
    IsUnit
      (infinityToFormalCurve
        N13IntegralInfinityChart.tClass) := by
  rw [infinityToFormalCurve_tClass]
  exact
    (tPowUnit 1).isUnit.map
      (algebraMap Laurent FormalCurve)
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The completion map restricts to the prescribed infinity-chart map. -/
@[simp] theorem ordinaryToFormalCurve_comp_infinity :
    ordinaryToFormalCurve.comp
        (algebraMap OrdinaryInfinityCurve OrdinaryOverlap) =
      infinityToFormalCurve := by
  exact
    IsLocalization.Away.lift_comp
      N13IntegralInfinityChart.tClass
      infinity_tClass_isUnit
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem ordinaryToFormalCurve_algebraMap
    (z : OrdinaryInfinityCurve) :
    ordinaryToFormalCurve
        (algebraMap OrdinaryInfinityCurve OrdinaryOverlap z) =
      infinityToFormalCurve z :=
  DFunLike.congr_fun ordinaryToFormalCurve_comp_infinity z
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem overlapBranches_infinity (b : B) :
    overlapBranches (algebraMap B O b) =
      (includePower (N13InfinityChartMarking.positiveExpansion b),
        includePower (N13InfinityChartMarking.negativeExpansion b)) := by
  change N13TwoAdicAffineRestrictionCompatibility.laurentPairMap
    (N13FormalOverlapSplit.formalBranchEval
      (N13OrdinaryCompletionCompatibility.ordinaryToFormalCurve
        (algebraMap B O b))) = _
  rw [N13OrdinaryCompletionCompatibility.ordinaryToFormalCurve_algebraMap]
  change N13TwoAdicAffineRestrictionCompatibility.laurentPairMap
    (N13FormalOverlapSplit.formalBranchEval
      (N13FormalInfinityChart.infinityToFormalCurve
        (N13IntegralInfinityChart.toFormalInfinity b))) = _
  rw [N13FormalOverlapSplit.formalBranchEval_infinityToFormalCurve]
  apply Prod.ext
  · exact N13TwoAdicInfinityCompatibility.laurentMap_includePower
      (N13InfinityChartMarking.positiveIntegralExpansion b)
  · exact N13TwoAdicInfinityCompatibility.laurentMap_includePower
      (N13InfinityChartMarking.negativeIntegralExpansion b)
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem positiveOverlap_infinity (b : B) :
    positiveOverlap (algebraMap B O b) =
      includePower (N13InfinityChartMarking.positiveExpansion b) :=
  congrArg Prod.fst (overlapBranches_infinity b)
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem negativeOverlap_infinity (b : B) :
    negativeOverlap (algebraMap B O b) =
      includePower (N13InfinityChartMarking.negativeExpansion b) :=
  congrArg Prod.snd (overlapBranches_infinity b)
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem positiveOverlap_injective : Function.Injective positiveOverlap := by
  exact (HuangN13.N13OverlapBranchCompatibility.overlap_maps_injective).1
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem negativeOverlap_injective : Function.Injective negativeOverlap := by
  exact (HuangN13.N13OverlapBranchCompatibility.overlap_maps_injective).2
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem positiveExpansion_injective :
    Function.Injective N13InfinityChartMarking.positiveExpansion := by
  intro a b hab
  apply N13IntegralCurveProperties.infinity_to_overlap_injective
  apply positiveOverlap_injective
  simpa only [positiveOverlap_infinity] using congrArg includePower hab
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem negativeExpansion_injective :
    Function.Injective N13InfinityChartMarking.negativeExpansion := by
  intro a b hab
  apply N13IntegralCurveProperties.infinity_to_overlap_injective
  apply negativeOverlap_injective
  simpa only [negativeOverlap_infinity] using congrArg includePower hab
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Exact chart transport commutes with both branches, with no independent
choice of numerator, denominator, or rational function on either branch. -/
theorem branch_cross_relations (a b : A) (c d : B)
    (h : N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap B O c) :
    N13Infinity.coordinateToLaurent Q₂ (N13IntegralFractionalHull.integralToRational a) *
        includePower (N13InfinityChartMarking.positiveExpansion d) =
      N13Infinity.coordinateToLaurent Q₂ (N13IntegralFractionalHull.integralToRational b) *
        includePower (N13InfinityChartMarking.positiveExpansion c) ∧
    N13InfinityMinus.coordinateToLaurentMinus Q₂ (N13IntegralFractionalHull.integralToRational a) *
        includePower (N13InfinityChartMarking.negativeExpansion d) =
      N13InfinityMinus.coordinateToLaurentMinus Q₂ (N13IntegralFractionalHull.integralToRational b) *
        includePower (N13InfinityChartMarking.negativeExpansion c) := by
  exact HuangN13.N13OverlapBranchCompatibility.branch_cross_relations a b c d h
end
end MazurProof.N13OverlapBranchCompatibility
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
namespace MazurProof.N13PrincipalBranchIdeals
noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem includePower_injective : Function.Injective includePower :=
  HahnSeries.ofPowerSeries_injective
end
end MazurProof.N13PrincipalBranchIdeals
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalBranchIdeals
noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem includePower_ne_zero {f : QP} (hf : f ≠ 0) : includePower f ≠ 0 :=
  (map_ne_zero_iff includePower includePower_injective).mpr hf
end
end MazurProof.N13PrincipalBranchIdeals
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalBranchIdeals
noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem two_eq_C : (2 : L) = HahnSeries.C (2 : Q₂) := (map_ofNat _ 2).symm
end
end MazurProof.N13PrincipalBranchIdeals
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalBranchIdeals
noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem includePower_order (f : QP) (hf : f ≠ 0) :
    (includePower f).order = (f.order.toNat : ℤ) := by
  have hinc : includePower f ≠ 0 := includePower_ne_zero hf
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    change (HahnSeries.ofPowerSeries ℤ Q₂ f).coeff (f.order.toNat : ℤ) ≠ 0
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    exact PowerSeries.coeff_order hf
  · rw [HahnSeries.le_order_iff_forall hinc]
    intro j hj
    change ((f : LaurentSeries Q₂).coeff j) = 0
    rw [PowerSeries.coeff_coe]
    split_ifs with hneg
    · rfl
    · apply PowerSeries.coeff_of_lt_order_toNat
      have hj0 : 0 ≤ j := le_of_not_gt hneg
      have hjabs : (j.natAbs : ℤ) = j := Int.natAbs_of_nonneg hj0
      omega
end
end MazurProof.N13PrincipalBranchIdeals
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalBranchIdeals
noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem span_eq_order_power (f : QP) (hf : f ≠ 0) :
    Ideal.span ({f} : Set QP) = Ideal.span ({PowerSeries.X ^ f.order.toNat} : Set QP) := by
  conv_lhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f)]
  exact Ideal.span_singleton_mul_right_unit
    (PowerSeries.isUnit_divided_by_X_pow_order hf) _
end
end MazurProof.N13PrincipalBranchIdeals
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalBranchIdeals
noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem principal_power_ideal_eq_of_orders (f g : QP) (hf : f ≠ 0) (hg : g ≠ 0)
    (p q : ℕ)
    (h : (includePower f).order + (p : ℤ) = (includePower g).order + (q : ℤ)) :
    Ideal.span ({f} : Set QP) * Ideal.span ({PowerSeries.X ^ p} : Set QP) =
      Ideal.span ({g} : Set QP) * Ideal.span ({PowerSeries.X ^ q} : Set QP) := by
  rw [includePower_order f hf, includePower_order g hg] at h
  have hn : f.order.toNat + p = g.order.toNat + q := by omega
  rw [span_eq_order_power f hf, span_eq_order_power g hg,
    Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_mul_span_singleton, ← pow_add, ← pow_add, hn]
end
end MazurProof.N13PrincipalBranchIdeals
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalBranchIdeals
noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem scalar_order (n : ℕ) : ((2 : L) ^ n).order = 0 := by
  rw [two_eq_C, ← map_pow, HahnSeries.order_C]
end
end MazurProof.N13PrincipalBranchIdeals
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalBranchIdeals
noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem clear_cross
    (χ : F →+* L) (f a b : F) (c d : L) (n m : ℕ)
    (hb : b ≠ 0)
    (hf : (2 : F) ^ m * f * b = (2 : F) ^ n * a)
    (hcross : χ a * d = χ b * c) :
    (2 : L) ^ m * χ f * d = (2 : L) ^ n * c := by
  have hbχ : χ b ≠ 0 := by simpa only [map_zero] using χ.injective.ne hb
  apply mul_right_cancel₀ hbχ
  have hm := congrArg χ hf
  simp only [map_mul, map_pow, map_ofNat] at hm
  calc
    ((2 : L) ^ m * χ f * d) * χ b = ((2 : L) ^ m * χ f * χ b) * d := by ring
    _ = ((2 : L) ^ n * χ a) * d := by rw [hm]
    _ = (2 : L) ^ n * (χ a * d) := by ring
    _ = ((2 : L) ^ n * c) * χ b := by rw [hcross]; ring
end
end MazurProof.N13PrincipalBranchIdeals
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalBranchIdeals
noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem order_of_scaled_cross
    (f : Fˣ) (χ : F →+* L) (c d : QP) (hc : c ≠ 0) (hd : d ≠ 0)
    (n m : ℕ)
    (h : (2 : L) ^ m * χ (f : F) * includePower d = (2 : L) ^ n * includePower c) :
    (includePower c).order = (χ (f : F)).order + (includePower d).order := by
  have h2 : (2 : L) ≠ 0 := by rw [two_eq_C]; exact HahnSeries.C_ne_zero (by norm_num)
  have hf : χ (f : F) ≠ 0 := by simpa only [map_zero] using χ.injective.ne f.ne_zero
  have hc' : includePower c ≠ 0 := includePower_ne_zero hc
  have hd' : includePower d ≠ 0 := includePower_ne_zero hd
  have ho := congrArg HahnSeries.order h
  rw [HahnSeries.order_mul (mul_ne_zero (pow_ne_zero m h2) hf) hd',
    HahnSeries.order_mul (pow_ne_zero m h2) hf,
    HahnSeries.order_mul (pow_ne_zero n h2) hc', scalar_order, scalar_order] at ho
  omega
end
end MazurProof.N13PrincipalBranchIdeals
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalBranchIdeals
noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13PrincipalBranchIdeals.instAlgebraAR
/-- The exact common primitive fraction determines both branch order
differences, even before any line ideal is considered. -/
theorem branch_orders_of_primitive_presentation
    (f : Fˣ) (n m : ℕ) (a b : A) (c d : B)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hf : (2 : F) ^ m * (f : F) * algebraMap A F b =
      (2 : F) ^ n * algebraMap A F a)
    (hcross : N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap B O c) :
    (includePower (N13InfinityChartMarking.positiveExpansion c)).order =
        Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder Q₂).ordPlus f) +
          (includePower (N13InfinityChartMarking.positiveExpansion d)).order ∧
    (includePower (N13InfinityChartMarking.negativeExpansion c)).order =
        Multiplicative.toAdd ((N13InfinityMinus.negativeInfinityOrder Q₂).ordPlus f) +
          (includePower (N13InfinityChartMarking.negativeExpansion d)).order := by
  have hbF : algebraMap A F b ≠ 0 := by
    change algebraMap R F (N13IntegralFractionalHull.integralToRational b) ≠ 0
    have hbr : N13IntegralFractionalHull.integralToRational b ≠ 0 := by
      simpa only [map_zero] using N13IntegralFractionalHull.integralToRational_injective.ne hb
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hbr
  obtain ⟨hp, hm⟩ := branch_cross_relations a b c d hcross
  have hp' : N13Infinity.functionFieldToLaurent Q₂ (algebraMap A F a) *
      includePower (N13InfinityChartMarking.positiveExpansion d) =
    N13Infinity.functionFieldToLaurent Q₂ (algebraMap A F b) *
      includePower (N13InfinityChartMarking.positiveExpansion c) := by
    change N13Infinity.functionFieldToLaurent Q₂
        (algebraMap R F (N13IntegralFractionalHull.integralToRational a)) * _ =
      N13Infinity.functionFieldToLaurent Q₂
        (algebraMap R F (N13IntegralFractionalHull.integralToRational b)) * _
    simpa only [N13Infinity.functionFieldToLaurent_algebraMap] using hp
  have hm' : N13InfinityMinus.functionFieldToLaurentMinus Q₂ (algebraMap A F a) *
      includePower (N13InfinityChartMarking.negativeExpansion d) =
    N13InfinityMinus.functionFieldToLaurentMinus Q₂ (algebraMap A F b) *
      includePower (N13InfinityChartMarking.negativeExpansion c) := by
    change N13InfinityMinus.functionFieldToLaurentMinus Q₂
        (algebraMap R F (N13IntegralFractionalHull.integralToRational a)) * _ =
      N13InfinityMinus.functionFieldToLaurentMinus Q₂
        (algebraMap R F (N13IntegralFractionalHull.integralToRational b)) * _
    simpa only [N13InfinityMinus.functionFieldToLaurentMinus_algebraMap] using hm
  constructor
  · exact order_of_scaled_cross f (N13Infinity.functionFieldToLaurent Q₂) _ _
      (by simpa only [map_zero] using positiveExpansion_injective.ne hc)
      (by simpa only [map_zero] using positiveExpansion_injective.ne hd) n m
      (clear_cross _ _ _ _ _ _ n m hbF hf hp')
  · exact order_of_scaled_cross f (N13InfinityMinus.functionFieldToLaurentMinus Q₂) _ _
      (by simpa only [map_zero] using negativeExpansion_injective.ne hc)
      (by simpa only [map_zero] using negativeExpansion_injective.ne hd) n m
      (clear_cross _ _ _ _ _ _ n m hbF hf hm')
end
end MazurProof.N13PrincipalBranchIdeals
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalBranchIdeals
noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
open N13InfinityChartMarking hiding B QP
open N13EffectiveInfinityRepair
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13PrincipalBranchIdeals.instAlgebraAR
/-- The affine principal relation and its positive orientation force BOTH
actual branch ideal equations for the transported common numerator and
denominator. The negative equation is derived from the norm/degree theorem;
it is not an additional compatibility hypothesis. -/
theorem tensor_branch_ideal_equations
    (E₀ E₁ E₂ E₃ : N13Mumford.SemiMumford Q₂)
    (h₀ : EffectiveChamber E₀) (h₁ : EffectiveChamber E₁)
    (h₂ : EffectiveChamber E₂) (h₃ : EffectiveChamber E₃)
    (L₀ L₁ L₂ L₃ : N13TwoChartPicardRealization.Line)
    (hL₀ : HasInfinityMultiplicities L₀ (positiveMultiplicity E₀) (negativeMultiplicity E₀))
    (hL₁ : HasInfinityMultiplicities L₁ (positiveMultiplicity E₁) (negativeMultiplicity E₁))
    (hL₂ : HasInfinityMultiplicities L₂ (positiveMultiplicity E₂) (negativeMultiplicity E₂))
    (hL₃ : HasInfinityMultiplicities L₃ (positiveMultiplicity E₃) (negativeMultiplicity E₃))
    (f : Fˣ) (n m : ℕ) (a b : A) (c d : B)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hf : (2 : F) ^ m * (f : F) * algebraMap A F b =
      (2 : F) ^ n * algebraMap A F a)
    (hcross : N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap B O c)
    (hprincipal :
      SexticMumford.mumfordIdealUnit (N13Mumford.model Q₂) E₀ *
        SexticMumford.mumfordIdealUnit (N13Mumford.model Q₂) E₁ *
        toPrincipalIdeal R F f =
      SexticMumford.mumfordIdealUnit (N13Mumford.model Q₂) E₂ *
        SexticMumford.mumfordIdealUnit (N13Mumford.model Q₂) E₃)
    (horientation : E₀.nInf + E₁.nInf +
      Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder Q₂).ordPlus f) =
        E₂.nInf + E₃.nInf) :
    Ideal.map positiveExpansion
        (Ideal.span ({c} : Set B) * (L₀.infinityIdeal * L₁.infinityIdeal)) =
      Ideal.map positiveExpansion
        (Ideal.span ({d} : Set B) * (L₂.infinityIdeal * L₃.infinityIdeal)) ∧
    Ideal.map negativeExpansion
        (Ideal.span ({c} : Set B) * (L₀.infinityIdeal * L₁.infinityIdeal)) =
      Ideal.map negativeExpansion
        (Ideal.span ({d} : Set B) * (L₂.infinityIdeal * L₃.infinityIdeal)) := by
  obtain ⟨hplus, hminus⟩ :=
    branch_orders_of_primitive_presentation f n m a b c d hb hc hd hf hcross
  have hbalance := N13PrincipalBranchBalance.principal_branch_orders_sum
    E₀ E₁ E₂ E₃ f hprincipal
  have hp₀ := positiveMultiplicity_cast E₀ h₀
  have hp₁ := positiveMultiplicity_cast E₁ h₁
  have hp₂ := positiveMultiplicity_cast E₂ h₂
  have hp₃ := positiveMultiplicity_cast E₃ h₃
  have hm₀ := negativeMultiplicity_cast E₀ h₀
  have hm₁ := negativeMultiplicity_cast E₁ h₁
  have hm₂ := negativeMultiplicity_cast E₂ h₂
  have hm₃ := negativeMultiplicity_cast E₃ h₃
  constructor
  · have he := principal_power_ideal_eq_of_orders
      (positiveExpansion c) (positiveExpansion d)
      (by simpa only [map_zero] using positiveExpansion_injective.ne hc)
      (by simpa only [map_zero] using positiveExpansion_injective.ne hd)
      (positiveMultiplicity E₀ + positiveMultiplicity E₁)
      (positiveMultiplicity E₂ + positiveMultiplicity E₃) (by push_cast; omega)
    simpa only [Ideal.map_mul, Ideal.map_span, Set.image_singleton,
      hL₀.1, hL₁.1, hL₂.1, hL₃.1,
      Ideal.span_singleton_mul_span_singleton, ← pow_add] using he
  · have he := principal_power_ideal_eq_of_orders
      (negativeExpansion c) (negativeExpansion d)
      (by simpa only [map_zero] using negativeExpansion_injective.ne hc)
      (by simpa only [map_zero] using negativeExpansion_injective.ne hd)
      (negativeMultiplicity E₀ + negativeMultiplicity E₁)
      (negativeMultiplicity E₂ + negativeMultiplicity E₃) (by push_cast; omega)
    simpa only [Ideal.map_mul, Ideal.map_span, Set.image_singleton,
      hL₀.2, hL₁.2, hL₂.2, hL₃.2,
      Ideal.span_singleton_mul_span_singleton, ← pow_add] using he
end
end MazurProof.N13PrincipalBranchIdeals
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13PrincipalBranchIdeals.instAlgebraAR MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    (E₀ E₁ E₂ E₃ : MazurProof.N13Mumford.SemiMumford MazurProof.N13OverlapBranchCompatibility.Q₂)
    (h₀ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₀) (h₁ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₁)
    (h₂ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₂) (h₃ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₃)
    (L₀ L₁ L₂ L₃ : MazurProof.N13TwoChartPicardRealization.Line)
    (hL₀ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities L₀ (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₀) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₀))
    (hL₁ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities L₁ (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₁) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₁))
    (hL₂ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities L₂ (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₂) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₂))
    (hL₃ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities L₃ (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₃) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₃))
    (f : MazurProof.N13PrincipalBranchIdeals.Fˣ) (n m : ℕ) (a b : MazurProof.N13OverlapBranchCompatibility.A) (c d : MazurProof.N13OverlapBranchCompatibility.B)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hf : (2 : MazurProof.N13PrincipalBranchIdeals.F) ^ m * (f : MazurProof.N13PrincipalBranchIdeals.F) * algebraMap MazurProof.N13OverlapBranchCompatibility.A MazurProof.N13PrincipalBranchIdeals.F b =
      (2 : MazurProof.N13PrincipalBranchIdeals.F) ^ n * algebraMap MazurProof.N13OverlapBranchCompatibility.A MazurProof.N13PrincipalBranchIdeals.F a)
    (hcross : MazurProof.N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O d =
      MazurProof.N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O c)
    (hprincipal :
      MazurProof.SexticMumford.mumfordIdealUnit (MazurProof.N13Mumford.model MazurProof.N13OverlapBranchCompatibility.Q₂) E₀ *
        MazurProof.SexticMumford.mumfordIdealUnit (MazurProof.N13Mumford.model MazurProof.N13OverlapBranchCompatibility.Q₂) E₁ *
        toPrincipalIdeal MazurProof.N13PrincipalBranchIdeals.R MazurProof.N13PrincipalBranchIdeals.F f =
      MazurProof.SexticMumford.mumfordIdealUnit (MazurProof.N13Mumford.model MazurProof.N13OverlapBranchCompatibility.Q₂) E₂ *
        MazurProof.SexticMumford.mumfordIdealUnit (MazurProof.N13Mumford.model MazurProof.N13OverlapBranchCompatibility.Q₂) E₃)
    (horientation : E₀.nInf + E₁.nInf +
      Multiplicative.toAdd ((MazurProof.N13Infinity.positiveInfinityOrder MazurProof.N13OverlapBranchCompatibility.Q₂).ordPlus f) =
        E₂.nInf + E₃.nInf) :
    Ideal.map MazurProof.N13InfinityChartMarking.positiveExpansion
        (Ideal.span ({c} : Set MazurProof.N13OverlapBranchCompatibility.B) * (L₀.infinityIdeal * L₁.infinityIdeal)) =
      Ideal.map MazurProof.N13InfinityChartMarking.positiveExpansion
        (Ideal.span ({d} : Set MazurProof.N13OverlapBranchCompatibility.B) * (L₂.infinityIdeal * L₃.infinityIdeal)) ∧
    Ideal.map MazurProof.N13InfinityChartMarking.negativeExpansion
        (Ideal.span ({c} : Set MazurProof.N13OverlapBranchCompatibility.B) * (L₀.infinityIdeal * L₁.infinityIdeal)) =
      Ideal.map MazurProof.N13InfinityChartMarking.negativeExpansion
        (Ideal.span ({d} : Set MazurProof.N13OverlapBranchCompatibility.B) * (L₂.infinityIdeal * L₃.infinityIdeal)) := by
  exact MazurProof.N13PrincipalBranchIdeals.tensor_branch_ideal_equations E₀ E₁ E₂ E₃ h₀ h₁ h₂ h₃ L₀ L₁ L₂ L₃ hL₀ hL₁ hL₂ hL₃ f n m a b c d hb hc hd hf hcross hprincipal horientation

-- Prove2me | solution 1 for MazurProof.N13Mumford.principal_between_balanced_of_constant
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:47:28.572027+00:00
-- url     : https://prove2.me/submissions/5b2a0dbd-f674-4b5c-a21b-f490fdb6c8ec

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_ker_mumfordEval
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_ker_mumfordEval
import Theorems.Thm_MazurProof_SexticMumford_ker_mumfordEval
import Theorems.Thm_MazurProof_SexticMumford_mumford_root_relation

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
/-!
# Integral generalized Mumford graph quotients for N13

For the good equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`,

evaluation on a graph `Y=v mod u` identifies the graph quotient with
`R[X]/(u)` over any nontrivial commutative base ring.  If the base is a
domain and `u` is monic, this quotient is free and hence torsion-free.
Consequently every graph ideal is saturated with respect to each nonzero
base scalar.

This is the elementary integral algebra needed before reduction modulo two;
it uses neither normality of the affine ring nor a Picard scheme.
-/
open Polynomial
namespace MazurProof.N13GeneralizedMumfordIntegral
noncomputable section
universe u
variable {R : Type u} [CommRing R]
@[simp] theorem mumfordEval_yClass
    (D : SemiMumford (R := R)) :
    mumfordEval D yClass =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v :=
  AdjoinRoot.lift_root (mumford_root_relation D)
namespace TwoAdic
end TwoAdic
end
end MazurProof.N13GeneralizedMumfordIntegral
end

end

-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
/-!
# The affine coordinate ring of the N13 good fibre at two

The good characteristic-two equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

defines a quadratic extension of `F₂(X)`.  This file constructs its affine
coordinate ring as an `AdjoinRoot` and proves irreducibility structurally.
The proof uses degree dominance and two coefficient comparisons; it does not
enumerate polynomials over `F₂`.
-/
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
@[simp] theorem mumfordEval_yClass (D : SemiMumford) :
    mumfordEval D yClass =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v :=
  AdjoinRoot.lift_root (mumford_root_relation D)
end
end MazurProof.N13GoodCoordinateRingTwo
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
@[simp] theorem mumfordEval_yClass (D : SemiMumford M) :
    mumfordEval M D (yClass M) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v := by
  exact AdjoinRoot.lift_root (mumford_root_relation M D)
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

-- ===== FLT.Assumptions.MazurProof.N13InfinityAPI =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityAPI =====
section
/-!
# Evaluation API for the positive infinity embedding of the N13 sextic
-/
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
@[simp] theorem functionFieldToLaurent_functionConstUnit (c : Kˣ) :
    functionFieldToLaurent K (functionConstUnit K c :
      N13Mumford.FunctionField K) =
      algebraMap K (LaurentSeries K) (c : K) := by
  change functionFieldToLaurent K
      (algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (algebraMap K (N13Mumford.CoordinateRing K) (c : K))) = _
  rw [functionFieldToLaurent_algebraMap, coordinateToLaurent_scalar]
@[simp] theorem ordPlus_functionConstUnit (c : Kˣ) :
    (positiveInfinityOrder K).ordPlus (functionConstUnit K c) = 1 := by
  change Multiplicative.ofAdd
      ((functionFieldToLaurent K
        (functionConstUnit K c : N13Mumford.FunctionField K)).order) = 1
  rw [functionFieldToLaurent_functionConstUnit]
  simp [HahnSeries.algebraMap_apply', HahnSeries.order_single c.ne_zero]
@[simp] theorem principalIdeal_functionConstUnit (c : Kˣ) :
    toPrincipalIdeal (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K) (functionConstUnit K c) = 1 := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change FractionalIdeal.spanSingleton
      (N13Mumford.CoordinateRing K)⁰
      (algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (coordinateConstUnit K c : N13Mumford.CoordinateRing K)) = 1
  rw [← FractionalIdeal.spanSingleton_one]
  apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
  refine ⟨(coordinateConstUnit K c)⁻¹, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, ← map_mul]
  change algebraMap (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K)
      (((coordinateConstUnit K c)⁻¹ :
          (N13Mumford.CoordinateRing K)ˣ) * coordinateConstUnit K c :
        (N13Mumford.CoordinateRing K)ˣ) = 1
  simp
end
end MazurProof.N13Infinity
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordRecover =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordRecover =====
section
/-!
# Recovering Mumford polynomials from their ideals

Contraction to the polynomial subring recovers the monic polynomial `u` from
the ideal `(u, Y - v)`, and the canonical remainder condition then recovers
`v`.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
theorem u_eq_of_mumfordIdeal_eq {D₁ D₂ : SemiMumford M}
    (h : mumfordIdeal M D₁.u D₁.v = mumfordIdeal M D₂.u D₂.v) :
    D₁.u = D₂.u := by
  have hc := congrArg (fun I : Ideal (CoordinateRing M) ↦
    I.comap (xClassHom M)) h
  rw [mumfordIdeal_comap_base M D₁, mumfordIdeal_comap_base M D₂] at hc
  exact eq_of_monic_of_associated D₁.u_monic D₂.u_monic
    (Ideal.span_singleton_eq_span_singleton.mp hc)
theorem v_eq_of_mumfordIdeal_eq_of_u_eq {D₁ D₂ : SemiMumford M}
    (hu : D₁.u = D₂.u)
    (h : mumfordIdeal M D₁.u D₁.v = mumfordIdeal M D₂.u D₂.v) :
    D₁.v = D₂.v := by
  have hy₂ : ySubClass M D₂.v ∈ mumfordIdeal M D₁.u D₁.v := by
    rw [h]
    exact Ideal.subset_span (by simp)
  have hker : ySubClass M D₂.v ∈ RingHom.ker (mumfordEval M D₁) := by
    rw [ker_mumfordEval M D₁]
    exact hy₂
  have heval : mumfordEval M D₁ (ySubClass M D₂.v) = 0 :=
    RingHom.mem_ker.mp hker
  have hquot : Ideal.Quotient.mk (Ideal.span ({D₁.u} : Set K[X]))
      (D₁.v - D₂.v) = 0 := by
    simpa only [ySubClass, map_sub, mumfordEval_yClass,
      mumfordEval_xClass, sub_eq_zero] using heval
  have hdvd : D₁.u ∣ D₁.v - D₂.v :=
    Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
  have hmod : D₁.v % D₁.u = D₂.v % D₁.u :=
    mod_eq_of_dvd_sub hdvd
  rw [D₁.v_reduced, hu, D₂.v_reduced] at hmod
  exact hmod
theorem uv_eq_of_mumfordIdeal_eq {D₁ D₂ : SemiMumford M}
    (h : mumfordIdeal M D₁.u D₁.v = mumfordIdeal M D₂.u D₂.v) :
    D₁.u = D₂.u ∧ D₁.v = D₂.v := by
  have hu := u_eq_of_mumfordIdeal_eq M h
  exact ⟨hu, v_eq_of_mumfordIdeal_eq_of_u_eq M hu h⟩
theorem mumford_eq_of_ideal_eq_of_nInf_eq {D₁ D₂ : Mumford M}
    (hIdeal : mumfordIdeal M D₁.u D₁.v = mumfordIdeal M D₂.u D₂.v)
    (hInf : D₁.nInf = D₂.nInf) : D₁ = D₂ := by
  obtain ⟨hu, hv⟩ := uv_eq_of_mumfordIdeal_eq M
    (D₁ := D₁.toSemi) (D₂ := D₂.toSemi) hIdeal
  cases D₁
  cases D₂
  simp_all
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordRigidity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordRigidity =====
section
/-!
# Constant-principal rigidity for balanced `X₁(13)` Mumford data

Once a principal multiplier between two balanced representatives is known to
be constant, its fractional ideal and its order at the positive infinity are
both trivial.  The generic ideal-kernel calculation then recovers `u`, `v`,
and the infinity coordinate.

The remaining normal-form uniqueness problem is therefore geometric: prove
that a function with the relevant small pole bounds is constant.
-/
open scoped nonZeroDivisors
namespace MazurProof.N13Mumford
open SexticMumford
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem principal_between_balanced_of_constant
    {D₁ D₂ : Mumford K} {α : (FunctionField K)ˣ}
    (c : Kˣ)
    (hα : α = N13Infinity.functionConstUnit K c)
    (hIdeal :
      mumfordIdealUnit (model K) D₁.toSemi *
          toPrincipalIdeal (CoordinateRing K) (FunctionField K) α =
        mumfordIdealUnit (model K) D₂.toSemi)
    (hInf :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) *
          (N13Infinity.positiveInfinityOrder K).ordPlus α =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1)) :
    D₁ = D₂ := by
  subst α
  have hUnits :
      mumfordIdealUnit (model K) D₁.toSemi =
        mumfordIdealUnit (model K) D₂.toSemi := by
    simpa only [N13Infinity.principalIdeal_functionConstUnit, mul_one] using
      hIdeal
  have hFrac := congrArg
    (fun I : InvFrac (model K) ↦
      (I : FractionalIdeal (CoordinateRing K)⁰ (FunctionField K))) hUnits
  simp only [coe_mumfordIdealUnit] at hFrac
  have hIdeal' :
      mumfordIdeal (model K) D₁.u D₁.v =
        mumfordIdeal (model K) D₂.u D₂.v :=
    FractionalIdeal.coeIdeal_inj.mp hFrac
  have hInf' :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1) := by
    simpa only [N13Infinity.ordPlus_functionConstUnit, mul_one] using hInf
  have hz : ((D₁.nInf : ℤ) - 1) = ((D₂.nInf : ℤ) - 1) :=
    Multiplicative.ofAdd.injective hInf'
  have hn : D₁.nInf = D₂.nInf := by omega
  exact mumford_eq_of_ideal_eq_of_nInf_eq (model K) hIdeal' hn
end
end MazurProof.N13Mumford
end

end

theorem solution : type_of% @MazurProof.N13Mumford.principal_between_balanced_of_constant := @MazurProof.N13Mumford.principal_between_balanced_of_constant

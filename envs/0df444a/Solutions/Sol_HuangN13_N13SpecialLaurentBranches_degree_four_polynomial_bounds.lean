-- Prove2me | solution 1 for HuangN13.N13SpecialLaurentBranches.degree_four_polynomial_bounds
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:08:34.875736+00:00
-- url     : https://prove2.me/submissions/71569ca0-4887-4bb9-9236-12614da0fb91

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialLaurentBranchesCore
import Theorems.Thm_MazurProof_N13BranchNorm_evalPoly_ne_zero
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_hPoly_natDegree

set_option autoImplicit false

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
@[simp] theorem plus_xClass (p : K[X]) : plus (N13GoodCoordinateRingTwo.xClass p) = base p :=
  AdjoinRoot.lift_of _
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
@[simp] theorem minus_xClass (p : K[X]) : minus (N13GoodCoordinateRingTwo.xClass p) = base p :=
  AdjoinRoot.lift_of _
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
@[simp] theorem plus_yClass : plus N13GoodCoordinateRingTwo.yClass =
    t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₀ := AdjoinRoot.lift_root _
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
@[simp] theorem minus_yClass : minus N13GoodCoordinateRingTwo.yClass =
    t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₁ := AdjoinRoot.lift_root _
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
private theorem two_eq_zero : (2 : L) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (algebraMap K L) (show (2 : K) = 0 by decide)
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
private theorem base_X : base X = t⁻¹ := by
  simp only [base, N13BranchNorm.evalPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl

attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem y_branch_sum : plus N13GoodCoordinateRingTwo.yClass + minus N13GoodCoordinateRingTwo.yClass =
    -base N13GoodCoordinateRingTwo.hPoly := by
  rw [plus_yClass, minus_yClass, N13SpecialInfinityBranchJets.r₁_eq, map_sub, map_neg]
  have hh : includeSeries N13SpecialInfinityBranchJets.h = 1 + t ^ 2 + t ^ 3 := by
    simp [N13SpecialInfinityBranchJets.h, includeSeries, N13LaurentPolynomialOrder.parameter]
  rw [hh]
  simp only [N13GoodCoordinateRingTwo.hPoly, map_add, map_pow, map_one, base_X]
  change t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₀ +
      t⁻¹ ^ 3 * (-(1 + t ^ 2 + t ^ 3) - includeSeries N13SpecialInfinityBranchJets.r₀) =
    -(t⁻¹ ^ 3 + t⁻¹ + 1)
  field_simp [t_ne_zero]
  ring
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem y_branch_difference : plus N13GoodCoordinateRingTwo.yClass - minus N13GoodCoordinateRingTwo.yClass =
    base N13GoodCoordinateRingTwo.hPoly := by
  have hs := y_branch_sum
  calc
    plus N13GoodCoordinateRingTwo.yClass - minus N13GoodCoordinateRingTwo.yClass =
        -(plus N13GoodCoordinateRingTwo.yClass + minus N13GoodCoordinateRingTwo.yClass) +
          2 * plus N13GoodCoordinateRingTwo.yClass := by ring
    _ = _ := by rw [hs, neg_neg, two_eq_zero, zero_mul, add_zero]
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem linear_difference (p q : K[X]) :
    plus (N13SpecialAffineNorm.linear p q) - minus (N13SpecialAffineNorm.linear p q) =
      base (q * N13GoodCoordinateRingTwo.hPoly) := by
  simp only [N13SpecialAffineNorm.linear, map_add, map_mul, plus_xClass, minus_xClass]
  calc
    base p + base q * plus N13GoodCoordinateRingTwo.yClass -
        (base p + base q * minus N13GoodCoordinateRingTwo.yClass) =
      base q * (plus N13GoodCoordinateRingTwo.yClass - minus N13GoodCoordinateRingTwo.yClass) := by ring
    _ = _ := by rw [y_branch_difference]
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
private theorem lower_order_sub (u v : L) (d : ℕ)
    (hu : -(d : ℤ) ≤ u.order) (hv : -(d : ℤ) ≤ v.order) (hsub : u - v ≠ 0) :
    -(d : ℤ) ≤ (u - v).order := by
  rw [HahnSeries.le_order_iff_forall hsub]
  intro j hj
  rw [HahnSeries.coeff_sub,
    HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hj hu),
    HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hj hv), sub_self]
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
/-- In characteristic two the two infinity sheets still bound the ordinate
coefficient, because their difference is the degree-three polynomial h. -/
theorem ordinate_degree_bound (p q : K[X]) (hq : q ≠ 0) (d : ℕ)
    (hpoles : -(d : ℤ) ≤ (plus (N13SpecialAffineNorm.linear p q)).order)
    (hmoles : -(d : ℤ) ≤ (minus (N13SpecialAffineNorm.linear p q)).order) :
    q.natDegree + 3 ≤ d := by
  have hqh : q * N13GoodCoordinateRingTwo.hPoly ≠ 0 :=
    mul_ne_zero hq N13GoodCoordinateRingTwo.hPoly_monic.ne_zero
  have hdiff : plus (N13SpecialAffineNorm.linear p q) - minus (N13SpecialAffineNorm.linear p q) ≠ 0 := by
    rw [linear_difference]
    exact N13BranchNorm.evalPoly_ne_zero K hqh
  have hb := lower_order_sub _ _ d hpoles hmoles hdiff
  rw [linear_difference, N13BranchNorm.evalPoly_order K _ hqh,
    Polynomial.natDegree_mul hq N13GoodCoordinateRingTwo.hPoly_monic.ne_zero,
    N13GoodCoordinateRingTwo.hPoly_natDegree, Nat.cast_add] at hb
  omega
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem include_order_nonnegative (r : P) : 0 ≤ (includeSeries r).order := by
  by_cases hr : r = 0
  · simp [hr]
  · have hinc : includeSeries r ≠ 0 :=
      (map_ne_zero_iff includeSeries HahnSeries.ofPowerSeries_injective).mpr hr
    rw [HahnSeries.le_order_iff_forall hinc]
    intro j hj
    change ((r : LaurentSeries K).coeff j) = 0
    rw [PowerSeries.coeff_coe, if_pos hj]
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
private theorem ordinate_term_lower (q : K[X]) (hq : q ≠ 0) (d : ℕ)
    (hqd : q.natDegree + 3 ≤ d) :
    -(d : ℤ) ≤ (base q * plus N13GoodCoordinateRingTwo.yClass).order := by
  by_cases hy : plus N13GoodCoordinateRingTwo.yClass = 0
  · simp [hy]
  · have hr : includeSeries N13SpecialInfinityBranchJets.r₀ ≠ 0 := by
      intro hr
      apply hy
      rw [plus_yClass, hr, mul_zero]
    have hyo := HahnSeries.order_mul (pow_ne_zero 3 (inv_ne_zero t_ne_zero)) hr
    rw [← plus_yClass, N13LaurentPolynomialOrder.order_parameter_inv_pow] at hyo
    have hr0 := include_order_nonnegative N13SpecialInfinityBranchJets.r₀
    rw [HahnSeries.order_mul (N13BranchNorm.evalPoly_ne_zero K hq) hy,
      N13BranchNorm.evalPoly_order K q hq, hyo]
    omega
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
/-- Both infinity pole bounds give the literal small-polynomial numerator
space needed for the degree-four finite check, without any enumeration. -/
theorem polynomial_bounds_of_two_poles (p q : K[X]) (d : ℕ)
    (hpoles : -(d : ℤ) ≤ (plus (N13SpecialAffineNorm.linear p q)).order)
    (hmoles : -(d : ℤ) ≤ (minus (N13SpecialAffineNorm.linear p q)).order) :
    p.natDegree ≤ d ∧ (q = 0 ∨ q.natDegree + 3 ≤ d) := by
  have hqbound : q = 0 ∨ q.natDegree + 3 ≤ d := by
    by_cases hq : q = 0
    · exact Or.inl hq
    · exact Or.inr (ordinate_degree_bound p q hq d hpoles hmoles)
  refine ⟨?_, hqbound⟩
  by_cases hp : p = 0
  · simp [hp]
  · by_cases hq : q = 0
    · have hb : -(d : ℤ) ≤ (base p).order := by
        simpa [N13SpecialAffineNorm.linear, hq] using hpoles
      rw [N13BranchNorm.evalPoly_order K p hp] at hb
      omega
    · have hqd : q.natDegree + 3 ≤ d := hqbound.resolve_left hq
      have hterm := ordinate_term_lower q hq d hqd
      have he : plus (N13SpecialAffineNorm.linear p q) -
          base q * plus N13GoodCoordinateRingTwo.yClass = base p := by
        simp only [N13SpecialAffineNorm.linear, map_add, map_mul, plus_xClass]
        ring
      have hne : plus (N13SpecialAffineNorm.linear p q) -
          base q * plus N13GoodCoordinateRingTwo.yClass ≠ 0 := by
        rw [he]
        exact N13BranchNorm.evalPoly_ne_zero K hp
      have hb := lower_order_sub _ _ d hpoles hterm hne
      rw [he, N13BranchNorm.evalPoly_order K p hp] at hb
      omega
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem degree_four_polynomial_bounds (p q : K[X])
    (hpoles : (-4 : ℤ) ≤ (plus (N13SpecialAffineNorm.linear p q)).order)
    (hmoles : (-4 : ℤ) ≤ (minus (N13SpecialAffineNorm.linear p q)).order) :
    p.natDegree ≤ 4 ∧ q.natDegree ≤ 1 := by
  obtain ⟨hp, hq⟩ := polynomial_bounds_of_two_poles p q 4 hpoles hmoles
  refine ⟨hp, ?_⟩
  rcases hq with hq | hq
  · simp [hq]
  · omega
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

open Polynomial
theorem solution (p q : MazurProof.N13SpecialLaurentBranches.K[X])
    (hpoles : (-4 : ℤ) ≤ (MazurProof.N13SpecialLaurentBranches.plus (MazurProof.N13SpecialAffineNorm.linear p q)).order)
    (hmoles : (-4 : ℤ) ≤ (MazurProof.N13SpecialLaurentBranches.minus (MazurProof.N13SpecialAffineNorm.linear p q)).order) :
    p.natDegree ≤ 4 ∧ q.natDegree ≤ 1 := by
  exact MazurProof.N13SpecialLaurentBranches.degree_four_polynomial_bounds p q hpoles hmoles

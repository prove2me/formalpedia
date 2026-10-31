-- Prove2me | solution 1 for HuangN13.N13SpecialDegreeFourCode.weightedLocalCode_eq_code_difference_icf
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:00:57.265978+00:00
-- url     : https://prove2.me/submissions/5385d66d-06f8-48c9-b759-8ca0633c1372

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DegreeFourStatementCore
import Definitions.Def_HuangN13_SeparationDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_infinity_sheet_difference_icf
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_recompose
import Theorems.Thm_MazurProof_N13SpecialAffineNorm_conjugate_linear

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof
namespace N13LaurentPolynomialOrder
noncomputable section
universe u
variable (K : Type u) [Field K]
@[simp] lemma order_parameter : (parameter K).order = 1 := by
  simp [parameter, HahnSeries.order_single]
end
end N13LaurentPolynomialOrder
end MazurProof
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem pointPolynomial_monic (P : CurvePoint) : (pointPolynomial P).Monic := by
  cases P
  · exact monic_X_sub_C _
  · exact monic_one
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem divisorPolynomial_monic (D : EffectiveDivisorTwo) : (divisorPolynomial D).Monic := by
  refine Sym2.inductionOn D ?_
  intro P Q
  exact (pointPolynomial_monic P).mul (pointPolynomial_monic Q)
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem tensorPolynomial_monic (D E : EffectiveDivisorTwo) : (tensorPolynomial D E).Monic :=
  (divisorPolynomial_monic D).mul (divisorPolynomial_monic E)
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
private theorem include_X : includeSeries (PowerSeries.X : N13SpecialLaurentBranches.P) = t :=
  HahnSeries.ofPowerSeries_X
end
end MazurProof.N13SpecialSmallNumerator
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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
private theorem include_unit_order (u : N13SpecialLaurentBranches.Pˣ) :
    (includeSeries (u : N13SpecialLaurentBranches.P)).order = 0 := by
  have hp : includeSeries (u : N13SpecialLaurentBranches.P) * includeSeries (↑(u⁻¹) : N13SpecialLaurentBranches.P) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have ho := HahnSeries.order_mul (u.isUnit.map includeSeries).ne_zero ((u⁻¹).isUnit.map includeSeries).ne_zero
  rw [hp, HahnSeries.order_one] at ho
  have hu := include_order_nonnegative (u : N13SpecialLaurentBranches.P)
  have hv := include_order_nonnegative (↑(u⁻¹) : N13SpecialLaurentBranches.P)
  omega
end
end MazurProof.N13SpecialSmallNumerator
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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
private theorem t_pow_order (n : ℕ) : (t ^ n).order = (n : ℤ) := by
  rw [HahnSeries.order_pow, N13LaurentPolynomialOrder.order_parameter]
  simp
end
end MazurProof.N13SpecialSmallNumerator
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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
theorem order_balance_of_principal_power_eq
    (f g : N13SpecialLaurentBranches.P) (hf : f ≠ 0) (hg : g ≠ 0) (n m : ℕ)
    (h : Ideal.span ({f} : Set N13SpecialLaurentBranches.P) * Ideal.span ({PowerSeries.X ^ n} : Set N13SpecialLaurentBranches.P) =
      Ideal.span ({g} : Set N13SpecialLaurentBranches.P) * Ideal.span ({PowerSeries.X ^ m} : Set N13SpecialLaurentBranches.P)) :
    (includeSeries f).order + (n : ℤ) = (includeSeries g).order + (m : ℤ) := by
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton] at h
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  have he := congrArg includeSeries hu
  simp only [map_mul, map_pow, include_X] at he
  have hf' : includeSeries f ≠ 0 :=
    (map_ne_zero_iff includeSeries HahnSeries.ofPowerSeries_injective).mpr hf
  have hg' : includeSeries g ≠ 0 :=
    (map_ne_zero_iff includeSeries HahnSeries.ofPowerSeries_injective).mpr hg
  have ho := congrArg HahnSeries.order he
  rw [HahnSeries.order_mul (mul_ne_zero hf' (pow_ne_zero n t_ne_zero)) (u.isUnit.map includeSeries).ne_zero,
    HahnSeries.order_mul hf' (pow_ne_zero n t_ne_zero),
    HahnSeries.order_mul hg' (pow_ne_zero m t_ne_zero),
    include_unit_order, t_pow_order, t_pow_order, add_zero] at ho
  exact ho
end
end MazurProof.N13SpecialSmallNumerator
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
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
@[simp] theorem divisorCode_mk
    (P Q : N13AbelFiberTwoModel.CurvePoint) :
    divisorCode s(P, Q) = pointCode P + pointCode Q := by
  rfl
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
private theorem beta_constant (p : K[X]) : PowerSeries.constantCoeff (beta p) = p.coeff 0 := by
  rw [beta_eq_coe, ← PowerSeries.coeff_zero_eq_constantCoeff]
  exact Polynomial.coeff_coe p 0
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
theorem rootZero_constant (a : K) : PowerSeries.constantCoeff (rootZero a) = 0 := by
  apply PowerSeries.X_dvd_iff.mp
  exact Ideal.mem_span_singleton.mp (Classical.choose_spec (exists_root_zero a)).2
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem rootOne_constant (a : K) : PowerSeries.constantCoeff (rootOne a) = 1 := by
  simp only [rootOne, map_sub, map_neg, beta_constant, hAt_constant, rootZero_constant, sub_zero]
  decide
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
@[simp] theorem branchZero_xClass (a : K) (p : K[X]) :
    branchZero a (N13GoodCoordinateRingTwo.xClass p) = evalBase a p := AdjoinRoot.lift_of _
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
@[simp] theorem branchOne_xClass (a : K) (p : K[X]) :
    branchOne a (N13GoodCoordinateRingTwo.xClass p) = evalBase a p := AdjoinRoot.lift_of _
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
@[simp] theorem branchZero_yClass (a : K) : branchZero a N13GoodCoordinateRingTwo.yClass = rootZero a :=
  AdjoinRoot.lift_root _
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
@[simp] theorem branchOne_yClass (a : K) : branchOne a N13GoodCoordinateRingTwo.yClass = rootOne a :=
  AdjoinRoot.lift_root _
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchFaithfulness
noncomputable section
open Polynomial N13SpecialFiniteBranchJets N13SpecialInfinityBranchJets
theorem shift_comp_cancel (p : K[X]) (a : K) :
    (p.comp (X + _root_.Polynomial.C a)).comp (X - _root_.Polynomial.C a) = p := by
  rw [Polynomial.comp_assoc]
  simp
end
end MazurProof.N13SpecialFiniteBranchFaithfulness
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchFaithfulness
noncomputable section
open Polynomial N13SpecialFiniteBranchJets N13SpecialInfinityBranchJets
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem evalBase_ne_zero (a : K) (p : K[X]) (hp : p ≠ 0) : evalBase a p ≠ 0 := by
  intro h
  have he : beta (p.comp (X + _root_.Polynomial.C a)) = 0 := (beta_comp a p).trans h
  have hpcomp : p.comp (X + _root_.Polynomial.C a) = 0 := by
    apply Polynomial.coe_injective K
    simpa only [beta_eq_coe, Polynomial.coe_zero] using he
  have hc := congrArg (fun q : K[X] => q.comp (X - _root_.Polynomial.C a)) hpcomp
  rw [shift_comp_cancel, Polynomial.zero_comp] at hc
  exact hp hc
end
end MazurProof.N13SpecialFiniteBranchFaithfulness
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchFaithfulness
noncomputable section
open Polynomial N13SpecialFiniteBranchJets N13SpecialInfinityBranchJets
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem branchZero_conjugate (a : K) (z : R) :
    branchZero a (N13SpecialAffineNorm.conjugate z) = branchOne a z := by
  have hz : z = N13SpecialAffineNorm.linear
      (N13GoodCoordinateRingTwo.coeff0 z) (N13GoodCoordinateRingTwo.coeffY z) :=
    (N13GoodCoordinateRingTwo.recompose z).symm
  rw [hz, N13SpecialAffineNorm.conjugate_linear]
  simp only [N13SpecialAffineNorm.linear, map_add, map_mul, map_sub, map_neg,
    branchZero_xClass, branchOne_xClass, branchZero_yClass, branchOne_yClass, rootOne]
  have hh : evalBase a N13GoodCoordinateRingTwo.hPoly = beta (hAt a) := (beta_comp a _).symm
  rw [hh]
  ring
end
end MazurProof.N13SpecialFiniteBranchFaithfulness
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchFaithfulness
noncomputable section
open Polynomial N13SpecialFiniteBranchJets N13SpecialInfinityBranchJets
theorem finite_branch_product (a : K) (z : R) :
    branchZero a z * branchOne a z = evalBase a (N13SpecialAffineNorm.norm z) := by
  rw [← branchZero_conjugate, ← map_mul, N13SpecialAffineNorm.mul_conjugate, branchZero_xClass]
end
end MazurProof.N13SpecialFiniteBranchFaithfulness
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchFaithfulness
noncomputable section
open Polynomial N13SpecialFiniteBranchJets N13SpecialInfinityBranchJets
theorem branchZero_ne_zero (a : K) (z : R) (hz : z ≠ 0) : branchZero a z ≠ 0 := by
  have hn := evalBase_ne_zero a _ (N13SpecialAffineNorm.norm_ne_zero z hz)
  rw [← finite_branch_product] at hn
  exact left_ne_zero_of_mul hn
end
end MazurProof.N13SpecialFiniteBranchFaithfulness
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchFaithfulness
noncomputable section
open Polynomial N13SpecialFiniteBranchJets N13SpecialInfinityBranchJets
theorem branchOne_ne_zero (a : K) (z : R) (hz : z ≠ 0) : branchOne a z ≠ 0 := by
  have hn := evalBase_ne_zero a _ (N13SpecialAffineNorm.norm_ne_zero z hz)
  rw [← finite_branch_product] at hn
  exact right_ne_zero_of_mul hn
end
end MazurProof.N13SpecialFiniteBranchFaithfulness
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchFaithfulness
noncomputable section
open Polynomial N13SpecialFiniteBranchJets N13SpecialInfinityBranchJets
def finiteBranch (a : K) (negative : Bool) : R →+* P :=
  if negative then branchOne a else branchZero a
end
end MazurProof.N13SpecialFiniteBranchFaithfulness
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchFaithfulness
noncomputable section
open Polynomial N13SpecialFiniteBranchJets N13SpecialInfinityBranchJets
theorem finiteBranch_ne_zero (a : K) (negative : Bool) (z : R) (hz : z ≠ 0) :
    finiteBranch a negative z ≠ 0 := by
  cases negative
  · exact branchZero_ne_zero a z hz
  · exact branchOne_ne_zero a z hz
end
end MazurProof.N13SpecialFiniteBranchFaithfulness
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchFaithfulness
noncomputable section
open Polynomial N13SpecialFiniteBranchJets N13SpecialInfinityBranchJets
@[simp] theorem finiteBranch_xClass (a : K) (negative : Bool) (p : K[X]) :
    finiteBranch a negative (N13GoodCoordinateRingTwo.xClass p) = evalBase a p := by
  cases negative <;> simp [finiteBranch]
end
end MazurProof.N13SpecialFiniteBranchFaithfulness
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchFaithfulness
noncomputable section
open Polynomial N13SpecialFiniteBranchJets N13SpecialInfinityBranchJets
theorem finiteBranch_y_constant (a : K) (negative : Bool) :
    PowerSeries.constantCoeff (finiteBranch a negative N13GoodCoordinateRingTwo.yClass) =
      (if negative then 1 else 0) := by
  cases negative <;> simp [finiteBranch, rootZero_constant, rootOne_constant]
end
end MazurProof.N13SpecialFiniteBranchFaithfulness
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFinitePointOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
theorem affine_point_branch_ideal (a : K) (negative : Bool) (P : AffinePoint) :
    Ideal.map (finiteBranch a negative) (affinePointIdeal P) =
      Ideal.span ({PowerSeries.X ^ finitePointOrder a negative (Sum.inl P)} : Set N13SpecialInfinityBranchJets.P) := by
  have he : Ideal.map (finiteBranch a negative) (affinePointIdeal P) =
      Ideal.span ({PowerSeries.X + PowerSeries.C a - PowerSeries.C P.1.1,
        finiteBranch a negative N13GoodCoordinateRingTwo.yClass - PowerSeries.C P.1.2} :
          Set N13SpecialInfinityBranchJets.P) := by
    simp [affinePointIdeal, N13GoodCoordinateRingTwo.mumfordIdeal,
      N13GoodCoordinateRingTwo.ySubClass, Ideal.map_span, Set.image_pair, evalBase]
  rw [he]
  simp only [finitePointOrder]
  by_cases hx : P.1.1 = a
  · by_cases hy : P.1.2 = (if negative then 1 else 0)
    · rw [if_pos ⟨hx, hy⟩, pow_one, hx, add_sub_cancel_right]
      apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
      apply PowerSeries.X_dvd_iff.mpr
      simp only [map_sub, PowerSeries.constantCoeff_C, finiteBranch_y_constant, hy, sub_self]
    · rw [if_neg (fun h => hy h.2), pow_zero, Ideal.span_singleton_one]
      have hu : IsUnit (finiteBranch a negative N13GoodCoordinateRingTwo.yClass - PowerSeries.C P.1.2) := by
        rw [PowerSeries.isUnit_iff_constantCoeff, map_sub, PowerSeries.constantCoeff_C, finiteBranch_y_constant]
        exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hy))
      exact (Ideal.span _).eq_top_of_isUnit_mem (Ideal.subset_span (by simp)) hu
  · rw [if_neg (fun h => hx h.1), pow_zero, Ideal.span_singleton_one]
    have hu : IsUnit (PowerSeries.X + PowerSeries.C a - PowerSeries.C P.1.1 : N13SpecialInfinityBranchJets.P) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simpa using (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hx)) : IsUnit (a - P.1.1))
    exact (Ideal.span _).eq_top_of_isUnit_mem (Ideal.subset_span (by simp)) hu
end
end MazurProof.N13SpecialFinitePointOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFinitePointOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
theorem point_branch_ideal (a : K) (negative : Bool) (P : CurvePoint) :
    Ideal.map (finiteBranch a negative) (point P).affineIdeal =
      Ideal.span ({PowerSeries.X ^ finitePointOrder a negative P} : Set N13SpecialInfinityBranchJets.P) := by
  cases P with
  | inl P =>
    simp only [point]
    split <;> exact affine_point_branch_ideal a negative P
  | inr P => simp [point, infinityPoint, finitePointOrder, Ideal.map_top]
end
end MazurProof.N13SpecialFinitePointOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFinitePointOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2
theorem divisor_branch_ideal (a : K) (negative : Bool) (D : EffectiveDivisorTwo) :
    Ideal.map (finiteBranch a negative) (ofDivisor D).affineIdeal =
      Ideal.span ({PowerSeries.X ^ finiteDivisorOrder a negative D} : Set N13SpecialInfinityBranchJets.P) := by
  refine Sym2.inductionOn D ?_
  intro P Q
  change Ideal.map (finiteBranch a negative) ((point P).affineIdeal * (point Q).affineIdeal) = _
  rw [Ideal.map_mul, point_branch_ideal, point_branch_ideal,
    Ideal.span_singleton_mul_span_singleton, ← pow_add]
  rfl
end
end MazurProof.N13SpecialFinitePointOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFinitePointOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2
def finiteTensorOrder (a : K) (negative : Bool) (D E : EffectiveDivisorTwo) : ℕ :=
  finiteDivisorOrder a negative D + finiteDivisorOrder a negative E
end
end MazurProof.N13SpecialFinitePointOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFinitePointOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2
theorem tensor_branch_ideal (a : K) (negative : Bool) (D E : EffectiveDivisorTwo) :
    Ideal.map (finiteBranch a negative) (tensor (ofDivisor D) (ofDivisor E)).affineIdeal =
      Ideal.span ({PowerSeries.X ^ finiteTensorOrder a negative D E} : Set N13SpecialInfinityBranchJets.P) := by
  change Ideal.map (finiteBranch a negative) ((ofDivisor D).affineIdeal * (ofDivisor E).affineIdeal) = _
  rw [Ideal.map_mul, divisor_branch_ideal, divisor_branch_ideal,
    Ideal.span_singleton_mul_span_singleton, ← pow_add]
  rfl
end
end MazurProof.N13SpecialFinitePointOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFinitePointOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2
theorem pointCode_eq_counts (P : CurvePoint) :
    N13SpecialAbelCode.pointCode P =
      (finitePointOrder 0 false P : ZMod 19) - finitePointOrder 0 true P +
        7 * (finitePointOrder 1 false P : ZMod 19) - 7 * finitePointOrder 1 true P +
        8 * (N13SpecialDivisorBranchOrders.pointOrder false P : ZMod 19) -
        8 * N13SpecialDivisorBranchOrders.pointOrder true P := by
  cases P with
  | inl P =>
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1.1 (ZMod.pow_card P.1.1) with hx | hx <;>
      rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1.2 (ZMod.pow_card P.1.2) with hy | hy <;>
      simp [N13SpecialAbelCode.pointCode, N13SpecialAbelCode.baseAmplitude,
        N13AbelFiberTwoModel.curvePointEquiv, finitePointOrder,
        N13SpecialDivisorBranchOrders.pointOrder, hx, hy]
  | inr P =>
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1 (ZMod.pow_card P.1) with hv | hv <;>
      simp [N13SpecialAbelCode.pointCode, N13SpecialAbelCode.baseAmplitude,
        N13AbelFiberTwoModel.curvePointEquiv, finitePointOrder,
        N13SpecialDivisorBranchOrders.pointOrder, hv]
end
end MazurProof.N13SpecialFinitePointOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFinitePointOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2
def countCode (D : EffectiveDivisorTwo) : ZMod 19 :=
  (finiteDivisorOrder 0 false D : ZMod 19) - finiteDivisorOrder 0 true D +
    7 * (finiteDivisorOrder 1 false D : ZMod 19) - 7 * finiteDivisorOrder 1 true D +
    8 * (N13SpecialDivisorBranchOrders.divisorOrder false D : ZMod 19) -
    8 * N13SpecialDivisorBranchOrders.divisorOrder true D
end
end MazurProof.N13SpecialFinitePointOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFinitePointOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2
theorem divisorCode_eq_counts (D : EffectiveDivisorTwo) : N13SpecialAbelCode.divisorCode D = countCode D := by
  refine Sym2.inductionOn D ?_
  intro P Q
  rw [N13SpecialAbelCode.divisorCode_mk, pointCode_eq_counts, pointCode_eq_counts]
  simp only [countCode, finiteDivisorOrder_mk, N13SpecialDivisorBranchOrders.divisorOrder_mk, Nat.cast_add]
  ring
end
end MazurProof.N13SpecialFinitePointOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialDegreeFourCode
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open N13SpecialDivisorCharts hiding K
open N13SpecialComparisonFactorPair hiding R
open N13SpecialDivisorBranchOrders N13SpecialSmallNumerator
open N13SpecialFiniteBranchFaithfulness hiding R
open N13SpecialFinitePointOrders N13SpecialSixJetOrders
private theorem include_ne_zero (p : P) (hp : p ≠ 0) : includeSeries p ≠ 0 := by
  have hne := (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)).ne hp
  rw [map_zero] at hne
  exact hne
end
end MazurProof.N13SpecialDegreeFourCode
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialDegreeFourCode
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open N13SpecialDivisorCharts hiding K
open N13SpecialComparisonFactorPair hiding R
open N13SpecialDivisorBranchOrders N13SpecialSmallNumerator
open N13SpecialFiniteBranchFaithfulness hiding R
open N13SpecialFinitePointOrders N13SpecialSixJetOrders
theorem finite_comparison_order_balance
    (a : K) (negative : Bool) (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H))) :
    (includeSeries (finiteBranch a negative h.aNum)).order + (finiteTensorOrder a negative D E : ℤ) =
      (includeSeries (finiteBranch a negative h.aDen)).order + (finiteTensorOrder a negative F H : ℤ) := by
  have he := congrArg (Ideal.map (finiteBranch a negative)) h.affine_eq
  simp only [Ideal.map_mul, Ideal.map_span, Set.image_singleton,
    N13SpecialFinitePointOrders.tensor_branch_ideal] at he
  exact order_balance_of_principal_power_eq _ _
    (finiteBranch_ne_zero a negative _ h.aNum_ne) (finiteBranch_ne_zero a negative _ h.aDen_ne) _ _ he
end
end MazurProof.N13SpecialDegreeFourCode
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialDegreeFourCode
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open N13SpecialDivisorCharts hiding K
open N13SpecialComparisonFactorPair hiding R
open N13SpecialDivisorBranchOrders N13SpecialSmallNumerator
open N13SpecialFiniteBranchFaithfulness hiding R
open N13SpecialFinitePointOrders N13SpecialSixJetOrders
theorem finite_cleared_order_balance
    (a : K) (negative : Bool) (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    (includeSeries (finiteBranch a negative z)).order + (finiteTensorOrder a negative D E : ℤ) =
      (finiteTensorOrder a negative F H : ℤ) +
        (includeSeries (N13SpecialFiniteBranchJets.evalBase a (tensorPolynomial D E))).order := by
  have hi := finite_comparison_order_balance a negative D E F H h
  have he := congrArg (includeSeries.comp (finiteBranch a negative)) hcross
  simp only [RingHom.comp_apply, map_mul, finiteBranch_xClass] at he
  have ho := congrArg HahnSeries.order he
  rw [HahnSeries.order_mul
      (include_ne_zero _ (finiteBranch_ne_zero a negative _ h.aNum_ne))
      (include_ne_zero _ (evalBase_ne_zero a _ (tensorPolynomial_monic D E).ne_zero)),
    HahnSeries.order_mul (include_ne_zero _ (finiteBranch_ne_zero a negative _ h.aDen_ne))
      (include_ne_zero _ (finiteBranch_ne_zero a negative z hz))] at ho
  omega
end
end MazurProof.N13SpecialDegreeFourCode
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialDegreeFourCode
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open N13SpecialDivisorCharts hiding K
open N13SpecialComparisonFactorPair hiding R
open N13SpecialDivisorBranchOrders N13SpecialSmallNumerator
open N13SpecialFiniteBranchFaithfulness hiding R
open N13SpecialFinitePointOrders N13SpecialSixJetOrders
theorem finite_sheet_difference
    (a : K) (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    (includeSeries (finiteBranch a false z)).order - (includeSeries (finiteBranch a true z)).order =
      ((finiteTensorOrder a false F H : ℤ) - finiteTensorOrder a true F H) -
        ((finiteTensorOrder a false D E : ℤ) - finiteTensorOrder a true D E) := by
  have hp := finite_cleared_order_balance a false D E F H h z hz hcross
  have hm := finite_cleared_order_balance a true D E F H h z hz hcross
  omega
end
end MazurProof.N13SpecialDegreeFourCode
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialDegreeFourCode
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open N13SpecialDivisorCharts hiding K
open N13SpecialComparisonFactorPair hiding R
open N13SpecialDivisorBranchOrders N13SpecialSmallNumerator
open N13SpecialFiniteBranchFaithfulness hiding R
open N13SpecialFinitePointOrders N13SpecialSixJetOrders
theorem weightedLocalCode_eq_code_difference
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    weightedLocalCode z =
      (N13SpecialAbelCode.divisorCode F + N13SpecialAbelCode.divisorCode H) -
        (N13SpecialAbelCode.divisorCode D + N13SpecialAbelCode.divisorCode E) := by
  have hzero := congrArg (fun n : ℤ => (n : ZMod 19)) (finite_sheet_difference 0 D E F H h z hz hcross)
  have hone := congrArg (fun n : ℤ => (n : ZMod 19)) (finite_sheet_difference 1 D E F H h z hz hcross)
  have hinfinity := congrArg (fun n : ℤ => (n : ZMod 19)) (HuangN13.N13SpecialDegreeFourCode.infinity_sheet_difference_icf D E F H h z hz hcross)
  push_cast at hzero hone hinfinity
  rw [divisorCode_eq_counts, divisorCode_eq_counts, divisorCode_eq_counts, divisorCode_eq_counts]
  change ((includeSeries (finiteBranch 0 false z)).order : ZMod 19) -
      ((includeSeries (finiteBranch 0 true z)).order : ZMod 19) +
      7 * ((includeSeries (finiteBranch 1 false z)).order : ZMod 19) -
      7 * ((includeSeries (finiteBranch 1 true z)).order : ZMod 19) +
      8 * ((plus z).order : ZMod 19) - 8 * ((minus z).order : ZMod 19) = _
  simp only [countCode, finiteTensorOrder, tensorOrder, Nat.cast_add] at hzero hone hinfinity ⊢
  linear_combination hzero + 7 * hone + 8 * hinfinity
end
end MazurProof.N13SpecialDegreeFourCode
end
end


set_option autoImplicit false
open Polynomial
theorem solution
    (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H)))
    (z : MazurProof.N13SpecialLaurentBranches.R) (hz : z ≠ 0)
    (hcross : h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) = h.aDen * z) :
    MazurProof.N13SpecialSixJetOrders.weightedLocalCode z =
      (MazurProof.N13SpecialAbelCode.divisorCode F + MazurProof.N13SpecialAbelCode.divisorCode H) -
        (MazurProof.N13SpecialAbelCode.divisorCode D + MazurProof.N13SpecialAbelCode.divisorCode E) := by
  exact MazurProof.N13SpecialDegreeFourCode.weightedLocalCode_eq_code_difference D E F H h z hz hcross

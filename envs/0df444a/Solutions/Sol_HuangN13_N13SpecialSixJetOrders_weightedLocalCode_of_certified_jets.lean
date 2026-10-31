-- Prove2me | solution 1 for HuangN13.N13SpecialSixJetOrders.weightedLocalCode_of_certified_jets
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:10:12.992931+00:00
-- url     : https://prove2.me/submissions/37aadb2d-f6f9-4dac-aae1-83139572075f

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialLaurentBranchesCore
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore
import Definitions.Def_HuangN13_SpecialJetCodeCore
import Definitions.Def_HuangN13_SixLocalOrdersCore
import Theorems.Thm_MazurProof_N13BranchNorm_evalPoly_ne_zero
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_recompose
import Theorems.Thm_MazurProof_N13LaurentPolynomialOrder_eval_parameter_eq_ofPowerSeries
import Theorems.Thm_MazurProof_N13SpecialAffineNorm_conjugate_linear

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
private theorem base_X : base X = t⁻¹ := by
  simp only [base, N13BranchNorm.evalPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl
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
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchZero_mem_xIdeal :
    branchZero ∈ xIdeal :=
  (Classical.choose_spec exists_branch_zero).2
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchZero_constantCoeff :
    PowerSeries.constantCoeff branchZero = 0 := by
  have hle :
      xIdeal ≤ RingHom.ker
        (PowerSeries.constantCoeff : Power →+* R₂) := by
    rw [xIdeal, Ideal.span_le]
    intro z hz
    subst z
    exact RingHom.mem_ker.mpr PowerSeries.constantCoeff_X
  exact RingHom.mem_ker.mp (hle branchZero_mem_xIdeal)
end
end MazurProof.N13FormalInfinityBranches
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem r₀_constant : PowerSeries.constantCoeff r₀ = 0 := by
  change PowerSeries.constantCoeff (PowerSeries.map PadicInt.toZMod
    N13FormalInfinityBranches.branchZero) = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    N13FormalInfinityBranches.branchZero_constantCoeff, map_zero]
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem r₁_constant : PowerSeries.constantCoeff r₁ = 1 := by
  rw [r₁_eq]
  norm_num [h, r₀_constant]
end
end MazurProof.N13SpecialInfinityBranchJets
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
theorem plus_conjugate (z : R) : plus (N13SpecialAffineNorm.conjugate z) = minus z := by
  have hz : z = N13SpecialAffineNorm.linear
      (N13GoodCoordinateRingTwo.coeff0 z) (N13GoodCoordinateRingTwo.coeffY z) :=
    (N13GoodCoordinateRingTwo.recompose z).symm
  rw [hz, N13SpecialAffineNorm.conjugate_linear]
  simp only [N13SpecialAffineNorm.linear, map_add, map_mul, plus_xClass, minus_xClass,
    map_sub, map_neg]
  linear_combination -(base (N13GoodCoordinateRingTwo.coeffY z)) * y_branch_sum
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
theorem branch_product (z : R) : plus z * minus z = base (N13SpecialAffineNorm.norm z) := by
  rw [← plus_conjugate, ← map_mul, N13SpecialAffineNorm.mul_conjugate, plus_xClass]
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
theorem plus_ne_zero (z : R) (hz : z ≠ 0) : plus z ≠ 0 := by
  have hn := N13BranchNorm.evalPoly_ne_zero K (N13SpecialAffineNorm.norm_ne_zero z hz)
  rw [← branch_product] at hn
  exact left_ne_zero_of_mul hn
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
theorem minus_ne_zero (z : R) (hz : z ≠ 0) : minus z ≠ 0 := by
  have hn := N13BranchNorm.evalPoly_ne_zero K (N13SpecialAffineNorm.norm_ne_zero z hz)
  rw [← branch_product] at hn
  exact right_ne_zero_of_mul hn
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
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem two_poly : (2 : K[X]) = 0 :=
  CharP.cast_eq_zero (K[X]) 2
end
end MazurProof.N13SpecialSmallFunctionCertificate
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
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
/-- The displayed polynomials really satisfy all six local equations to
nine-jet precision. The divisibility witnesses are explicit polynomials. -/
theorem jet_polynomials_satisfy_equations :
    (X : K[X]) ^ 9 ∣ residual N13GoodCoordinateRingTwo.hPoly N13GoodCoordinateRingTwo.rhsPoly jetZeroZero ∧
    (X : K[X]) ^ 9 ∣ residual N13GoodCoordinateRingTwo.hPoly N13GoodCoordinateRingTwo.rhsPoly jetZeroOne ∧
    (X : K[X]) ^ 9 ∣ residual (N13GoodCoordinateRingTwo.hPoly.comp (X + 1))
      (N13GoodCoordinateRingTwo.rhsPoly.comp (X + 1)) jetOneZero ∧
    (X : K[X]) ^ 9 ∣ residual (N13GoodCoordinateRingTwo.hPoly.comp (X + 1))
      (N13GoodCoordinateRingTwo.rhsPoly.comp (X + 1)) jetOneOne ∧
    (X : K[X]) ^ 9 ∣ residual N13SpecialInfinityChart.hPoly N13SpecialInfinityChart.rhsPoly jetInfinityZero ∧
    (X : K[X]) ^ 9 ∣ residual N13SpecialInfinityChart.hPoly N13SpecialInfinityChart.rhsPoly jetInfinityOne := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨X + X ^ 5, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (X ^ 7 + X ^ 8 + X ^ 11) * two_poly
  · refine ⟨X + X ^ 5, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (1 + 2 * X + X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4 + X ^ 5 + X ^ 6 + 3 * X ^ 7 + 2 * X ^ 8 + X ^ 10 + X ^ 11) * two_poly
  · refine ⟨1 + X ^ 2 + X ^ 3 + X ^ 7, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (-1 - 3 * X - 4 * X ^ 2 - X ^ 3 + 4 * X ^ 4 + 7 * X ^ 5 + 8 * X ^ 6 + 7 * X ^ 7 + 6 * X ^ 8 + 5 * X ^ 9 + 4 * X ^ 10 + 2 * X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14) * two_poly
  · refine ⟨1 + X ^ 2 + X ^ 3 + X ^ 7, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (1 - 4 * X ^ 2 - 5 * X ^ 3 + 5 * X ^ 5 + 7 * X ^ 6 + 5 * X ^ 7 + 5 * X ^ 8 + 4 * X ^ 9 + 3 * X ^ 10 + X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14) * two_poly
  · refine ⟨1 + X ^ 2 + X ^ 3 + X ^ 7, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + 3 * X ^ 6 + 3 * X ^ 7 + 3 * X ^ 8 + 3 * X ^ 9 + 2 * X ^ 10 + 2 * X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14) * two_poly
  · refine ⟨1 + X ^ 2 + X ^ 3 + X ^ 7, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (1 + X + 2 * X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4 + 3 * X ^ 5 + 4 * X ^ 6 + 3 * X ^ 7 + 4 * X ^ 8 + 2 * X ^ 9 + 3 * X ^ 10 + X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14) * two_poly
end
end MazurProof.N13SpecialSmallFunctionCertificate
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
namespace MazurProof.N13SpecialRootJetAgreement
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem root_jet_agreement (H R s : K[X]) (r : P) (n : ℕ)
    (hH : H.coeff 0 = 1)
    (hconstant : PowerSeries.constantCoeff r = s.coeff 0)
    (hr : r ^ 2 + beta H * r - beta R = 0)
    (hs : (X : K[X]) ^ n ∣ residual H R s) :
    (PowerSeries.X : P) ^ n ∣ r - beta s := by
  have hc (p : K[X]) : PowerSeries.constantCoeff (beta p) = p.coeff 0 := by
    rw [beta_eq_coe, ← PowerSeries.coeff_zero_eq_constantCoeff]
    exact Polynomial.coeff_coe p 0
  have hu : IsUnit (r + beta s + beta H) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_add, map_add, hconstant, hc, hc, hH]
    have htwo : s.coeff 0 + s.coeff 0 = 0 := by
      simpa only [two_mul, zero_mul] using
        congrArg (fun a : K => a * s.coeff 0) (show (2 : K) = 0 by decide)
    rw [htwo, zero_add]
    exact isUnit_one
  have hd : (PowerSeries.X : P) ^ n ∣ beta (residual H R s) := by
    obtain ⟨w, hw⟩ := hs
    refine ⟨beta w, ?_⟩
    rw [hw, map_mul, map_pow]
    simp [beta]
  have he : (r - beta s) * (r + beta s + beta H) = -beta (residual H R s) := by
    simp only [N13SpecialSmallFunctionCertificate.residual, map_sub, map_add, map_pow, map_mul]
    linear_combination hr
  have hprod : (PowerSeries.X : P) ^ n ∣ (r - beta s) * (r + beta s + beta H) := by
    rw [he]
    exact dvd_neg.mpr hd
  obtain ⟨u, hu⟩ := hu
  rw [← hu] at hprod
  obtain ⟨w, hw⟩ := hprod
  refine ⟨w * (↑(u⁻¹) : P), ?_⟩
  calc
    r - beta s = ((r - beta s) * (u : P)) * (↑(u⁻¹) : P) := by simp [mul_assoc]
    _ = (PowerSeries.X : P) ^ n * (w * (↑(u⁻¹) : P)) := by rw [hw]; ring
end
end MazurProof.N13SpecialRootJetAgreement
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialRootJetAgreement
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem infinity_zero_jet_agreement :
    (PowerSeries.X : P) ^ 9 ∣ r₀ - beta jetInfinityZero := by
  apply root_jet_agreement N13SpecialInfinityChart.hPoly N13SpecialInfinityChart.rhsPoly
    jetInfinityZero r₀ 9
  · simp [N13SpecialInfinityChart.hPoly]
  · simpa [jetInfinityZero] using r₀_constant
  · simpa [beta, N13SpecialInfinityChart.hPoly, N13SpecialInfinityChart.rhsPoly, h, rhs] using r₀_relation
  · exact jet_polynomials_satisfy_equations.2.2.2.2.1
end
end MazurProof.N13SpecialRootJetAgreement
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialRootJetAgreement
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem infinity_one_jet_agreement :
    (PowerSeries.X : P) ^ 9 ∣ r₁ - beta jetInfinityOne := by
  apply root_jet_agreement N13SpecialInfinityChart.hPoly N13SpecialInfinityChart.rhsPoly
    jetInfinityOne r₁ 9
  · simp [N13SpecialInfinityChart.hPoly]
  · simpa [jetInfinityOne] using r₁_constant
  · simpa [beta, N13SpecialInfinityChart.hPoly, N13SpecialInfinityChart.rhsPoly, h, rhs] using r₁_relation
  · exact jet_polynomials_satisfy_equations.2.2.2.2.2
end
end MazurProof.N13SpecialRootJetAgreement
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialRootJetAgreement
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem infinity_numerator_zero_jet (A B : K[X]) :
    (PowerSeries.X : P) ^ 9 ∣
      (beta A + beta B * r₀) - beta (A + B * jetInfinityZero) := by
  have hd := dvd_mul_of_dvd_right infinity_zero_jet_agreement (beta B)
  convert hd using 1 <;> simp only [map_add, map_mul] <;> ring
end
end MazurProof.N13SpecialRootJetAgreement
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialRootJetAgreement
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem infinity_numerator_one_jet (A B : K[X]) :
    (PowerSeries.X : P) ^ 9 ∣
      (beta A + beta B * r₁) - beta (A + B * jetInfinityOne) := by
  have hd := dvd_mul_of_dvd_right infinity_one_jet_agreement (beta B)
  convert hd using 1 <;> simp only [map_add, map_mul] <;> ring
end
end MazurProof.N13SpecialRootJetAgreement
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
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem zero_zero_jet : (PowerSeries.X : P) ^ 9 ∣ rootZero 0 - beta jetZeroZero := by
  apply N13SpecialRootJetAgreement.root_jet_agreement (hAt 0) (rhsAt 0) jetZeroZero _ 9
  · exact hAt_constant _
  · simpa [jetZeroZero] using rootZero_constant (0 : K)
  · exact rootZero_relation _
  · simpa [hAt, rhsAt] using jet_polynomials_satisfy_equations.1
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
theorem zero_one_jet : (PowerSeries.X : P) ^ 9 ∣ rootOne 0 - beta jetZeroOne := by
  apply N13SpecialRootJetAgreement.root_jet_agreement (hAt 0) (rhsAt 0) jetZeroOne _ 9
  · exact hAt_constant _
  · simpa [jetZeroOne] using rootOne_constant (0 : K)
  · exact rootOne_relation _
  · simpa [hAt, rhsAt] using jet_polynomials_satisfy_equations.2.1
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
theorem one_zero_jet : (PowerSeries.X : P) ^ 9 ∣ rootZero 1 - beta jetOneZero := by
  apply N13SpecialRootJetAgreement.root_jet_agreement (hAt 1) (rhsAt 1) jetOneZero _ 9
  · exact hAt_constant _
  · simpa [jetOneZero] using rootZero_constant (1 : K)
  · exact rootZero_relation _
  · simpa [hAt, rhsAt] using jet_polynomials_satisfy_equations.2.2.1
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
theorem one_one_jet : (PowerSeries.X : P) ^ 9 ∣ rootOne 1 - beta jetOneOne := by
  apply N13SpecialRootJetAgreement.root_jet_agreement (hAt 1) (rhsAt 1) jetOneOne _ 9
  · exact hAt_constant _
  · simpa [jetOneOne] using rootOne_constant (1 : K)
  · exact rootOne_relation _
  · simpa [hAt, rhsAt] using jet_polynomials_satisfy_equations.2.2.2.1
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialJetOrder
noncomputable section
open Polynomial N13SpecialInfinityBranchJets
open N13SpecialLaurentBranches hiding K P
open scoped LaurentSeries
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem coeff_eq_of_jet_congruence (r : P) (s : K[X]) (n : ℕ)
    (h : (PowerSeries.X : P) ^ n ∣ r - beta s) (j : ℕ) (hj : j < n) :
    PowerSeries.coeff j r = s.coeff j := by
  have hh := PowerSeries.X_pow_dvd_iff.mp h j hj
  rw [map_sub, beta_eq_coe, Polynomial.coeff_coe] at hh
  exact sub_eq_zero.mp hh
end
end MazurProof.N13SpecialJetOrder
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialJetOrder
noncomputable section
open Polynomial N13SpecialInfinityBranchJets
open N13SpecialLaurentBranches hiding K P
open scoped LaurentSeries
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem order_eq_of_certified_jet (r : P) (s : K[X]) (n k : ℕ)
    (hk : k < n) (hcoeff : s.coeff k ≠ 0)
    (hlow : ∀ j : ℕ, j < k → s.coeff j = 0)
    (hjet : (PowerSeries.X : P) ^ n ∣ r - beta s) :
    (includeSeries r).order = (k : ℤ) := by
  have hkr : PowerSeries.coeff k r ≠ 0 := by
    rwa [coeff_eq_of_jet_congruence r s n hjet k hk]
  have hr : r ≠ 0 := by
    intro h
    apply hkr
    simp [h]
  have hinc : includeSeries r ≠ 0 := by
    have hne := (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)).ne hr
    rw [map_zero] at hne
    exact hne
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    change (HahnSeries.ofPowerSeries ℤ K r).coeff (k : ℤ) ≠ 0
    rwa [HahnSeries.ofPowerSeries_apply_coeff]
  · rw [HahnSeries.le_order_iff_forall hinc]
    intro j hj
    change ((r : LaurentSeries K).coeff j) = 0
    rw [PowerSeries.coeff_coe]
    split_ifs with hneg
    · rfl
    · have hj0 : 0 ≤ j := le_of_not_gt hneg
      have hjabs : (j.natAbs : ℤ) = j := Int.natAbs_of_nonneg hj0
      have hjk : j.natAbs < k := by omega
      rw [coeff_eq_of_jet_congruence r s n hjet j.natAbs (lt_trans hjk hk)]
      exact hlow _ hjk
end
end MazurProof.N13SpecialJetOrder
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSixJetOrders
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
def sixSeries (a : Fin 5 → K) (b : Fin 2 → K) : Fin 6 → P := ![
  branchZero 0 (function a b), branchOne 0 (function a b),
  branchZero 1 (function a b), branchOne 1 (function a b),
  beta (infinityNumerator a) + beta (infinityOrdinate b) * r₀,
  beta (infinityNumerator a) + beta (infinityOrdinate b) * r₁]
end
end MazurProof.N13SpecialSixJetOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSixJetOrders
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
private theorem linear_jet (p q s : K[X]) (r : P)
    (h : (PowerSeries.X : P) ^ 9 ∣ r - beta s) :
    (PowerSeries.X : P) ^ 9 ∣ (beta p + beta q * r) - beta (p + q * s) := by
  have hh := dvd_mul_of_dvd_right h (beta q)
  convert hh using 1 <;> simp only [map_add, map_mul] <;> ring
end
end MazurProof.N13SpecialSixJetOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSixJetOrders
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
private theorem evalBase_zero (p : K[X]) : evalBase 0 p = beta p := by
  rw [← beta_comp]
  simp
end
end MazurProof.N13SpecialSixJetOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSixJetOrders
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
private theorem evalBase_one (p : K[X]) : evalBase 1 p = beta (p.comp (X + 1)) := by
  rw [← beta_comp]
  simp
end
end MazurProof.N13SpecialSixJetOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSixJetOrders
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem six_series_jet_congruence (a : Fin 5 → K) (b : Fin 2 → K) (i : Fin 6) :
    (PowerSeries.X : P) ^ 9 ∣ sixSeries a b i - beta (sixJetPolynomials a b i) := by
  fin_cases i
  · change (PowerSeries.X : P) ^ 9 ∣ branchZero 0 (function a b) - _
    simp only [function, N13SpecialAffineNorm.linear, map_add, map_mul,
      branchZero_xClass, branchZero_yClass, evalBase_zero]
    exact linear_jet _ _ _ _ zero_zero_jet
  · change (PowerSeries.X : P) ^ 9 ∣ branchOne 0 (function a b) - _
    simp only [function, N13SpecialAffineNorm.linear, map_add, map_mul,
      branchOne_xClass, branchOne_yClass, evalBase_zero]
    exact linear_jet _ _ _ _ zero_one_jet
  · change (PowerSeries.X : P) ^ 9 ∣ branchZero 1 (function a b) - _
    simp only [function, N13SpecialAffineNorm.linear, map_add, map_mul,
      branchZero_xClass, branchZero_yClass, evalBase_one]
    exact linear_jet _ _ _ _ one_zero_jet
  · change (PowerSeries.X : P) ^ 9 ∣ branchOne 1 (function a b) - _
    simp only [function, N13SpecialAffineNorm.linear, map_add, map_mul,
      branchOne_xClass, branchOne_yClass, evalBase_one]
    exact linear_jet _ _ _ _ one_one_jet
  · exact N13SpecialRootJetAgreement.infinity_numerator_zero_jet _ _
  · exact N13SpecialRootJetAgreement.infinity_numerator_one_jet _ _
end
end MazurProof.N13SpecialSixJetOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSixJetOrders
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
theorem six_series_orders (a : Fin 5 → K) (b : Fin 2 → K)
    (hjets : ∀ i : Fin 6, sixJetOrders a b i < 9 ∧
      (sixJetPolynomials a b i).coeff (sixJetOrders a b i) ≠ 0 ∧
      ∀ j : Fin 9, (j : ℕ) < sixJetOrders a b i → (sixJetPolynomials a b i).coeff j = 0)
    (i : Fin 6) : (includeSeries (sixSeries a b i)).order = (sixJetOrders a b i : ℤ) := by
  apply N13SpecialJetOrder.order_eq_of_certified_jet _ _ 9 _
    (hjets i).1 (hjets i).2.1 _ (six_series_jet_congruence a b i)
  intro j hj
  exact (hjets i).2.2 ⟨j, lt_trans hj (hjets i).1⟩ hj
end
end MazurProof.N13SpecialSixJetOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSixJetOrders
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
private theorem include_beta (p : K[X]) :
    includeSeries (beta p) = p.eval₂ (algebraMap K L) t := by
  rw [beta_eq_coe]
  exact (N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries K p).symm
end
end MazurProof.N13SpecialSixJetOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSixJetOrders
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
/-- The precise reciprocal change of coordinates, including t^4. -/
theorem reciprocal_numerator_identity (a : Fin 5 → K) (b : Fin 2 → K) (r : P) :
    t ^ 4 * (base (numerator a) + base (ordinate b) * (t⁻¹ ^ 3 * includeSeries r)) =
      includeSeries (beta (infinityNumerator a) + beta (infinityOrdinate b) * r) := by
  rw [map_add, map_mul, include_beta, include_beta]
  have hb : base = Polynomial.eval₂RingHom (algebraMap K L) t⁻¹ := rfl
  have hu : t * t⁻¹ = 1 := mul_inv_cancel₀ t_ne_zero
  rw [hb]
  generalize t⁻¹ = u at hu ⊢
  generalize t = s at hu ⊢
  simp only [numerator, ordinate, infinityNumerator, infinityOrdinate,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_finsetSum, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_X_pow,
    Fin.sum_univ_five]
  norm_num
  linear_combination (algebraMap K L (a 1) * s ^ 3 + algebraMap K L (a 2) * s ^ 2 * (s * u + 1) +
    algebraMap K L (a 3) * s * (s ^ 2 * u ^ 2 + s * u + 1) +
    (algebraMap K L (a 4) + algebraMap K L (b 1) * includeSeries r) *
      (s ^ 3 * u ^ 3 + s ^ 2 * u ^ 2 + s * u + 1) +
    algebraMap K L (b 0) * includeSeries r * s * (s ^ 2 * u ^ 2 + s * u + 1)) * hu
end
end MazurProof.N13SpecialSixJetOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSixJetOrders
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem six_orders_of_jets (a : Fin 5 → K) (b : Fin 2 → K)
    (hn : function a b ≠ 0)
    (hjets : ∀ i : Fin 6, sixJetOrders a b i < 9 ∧
      (sixJetPolynomials a b i).coeff (sixJetOrders a b i) ≠ 0 ∧
      ∀ j : Fin 9, (j : ℕ) < sixJetOrders a b i → (sixJetPolynomials a b i).coeff j = 0)
    (i : Fin 6) : sixOrders (function a b) i =
      (sixJetOrders a b i : ℤ) - (if (i : ℕ) < 4 then 0 else 4) := by
  have ho := six_series_orders a b hjets
  fin_cases i
  · simpa [sixOrders, sixSeries] using ho 0
  · simpa [sixOrders, sixSeries] using ho 1
  · simpa [sixOrders, sixSeries] using ho 2
  · simpa [sixOrders, sixSeries] using ho 3
  · have hr : t ^ 4 * plus (function a b) = includeSeries (sixSeries a b 4) := by
      change _ = includeSeries (beta (infinityNumerator a) + beta (infinityOrdinate b) * r₀)
      simpa only [function, N13SpecialAffineNorm.linear, map_add, map_mul, plus_xClass, plus_yClass]
        using reciprocal_numerator_identity a b r₀
    have horder := congrArg HahnSeries.order hr
    rw [HahnSeries.order_mul (pow_ne_zero 4 t_ne_zero) (plus_ne_zero _ hn),
      HahnSeries.order_pow, N13LaurentPolynomialOrder.order_parameter, ho] at horder
    change (plus (function a b)).order = (sixJetOrders a b 4 : ℤ) - 4
    norm_num at horder
    omega
  · have hr : t ^ 4 * minus (function a b) = includeSeries (sixSeries a b 5) := by
      change _ = includeSeries (beta (infinityNumerator a) + beta (infinityOrdinate b) * r₁)
      simpa only [function, N13SpecialAffineNorm.linear, map_add, map_mul, minus_xClass, minus_yClass]
        using reciprocal_numerator_identity a b r₁
    have horder := congrArg HahnSeries.order hr
    rw [HahnSeries.order_mul (pow_ne_zero 4 t_ne_zero) (minus_ne_zero _ hn),
      HahnSeries.order_pow, N13LaurentPolynomialOrder.order_parameter, ho] at horder
    change (minus (function a b)).order = (sixJetOrders a b 5 : ℤ) - 4
    norm_num at horder
    omega
end
end MazurProof.N13SpecialSixJetOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSixJetOrders
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
theorem weightedLocalCode_of_certified_jets (a : Fin 5 → K) (b : Fin 2 → K)
    (hn : function a b ≠ 0)
    (hjets : ∀ i : Fin 6, sixJetOrders a b i < 9 ∧
      (sixJetPolynomials a b i).coeff (sixJetOrders a b i) ≠ 0 ∧
      ∀ j : Fin 9, (j : ℕ) < sixJetOrders a b i → (sixJetPolynomials a b i).coeff j = 0)
    (hcode : weightedJetCode a b = 0) : weightedLocalCode (function a b) = 0 := by
  unfold weightedLocalCode
  simp only [six_orders_of_jets a b hn hjets]
  norm_num
  unfold weightedJetCode at hcode
  linear_combination hcode
end
end MazurProof.N13SpecialSixJetOrders
end
end

open Polynomial
theorem solution (a : Fin 5 → MazurProof.N13SpecialSmallFunctionCertificate.K) (b : Fin 2 → MazurProof.N13SpecialSmallFunctionCertificate.K)
    (hn : MazurProof.N13SpecialSixJetOrders.function a b ≠ 0)
    (hjets : ∀ i : Fin 6, MazurProof.N13SpecialSmallFunctionCertificate.sixJetOrders a b i < 9 ∧
      (MazurProof.N13SpecialSmallFunctionCertificate.sixJetPolynomials a b i).coeff (MazurProof.N13SpecialSmallFunctionCertificate.sixJetOrders a b i) ≠ 0 ∧
      ∀ j : Fin 9, (j : ℕ) < MazurProof.N13SpecialSmallFunctionCertificate.sixJetOrders a b i → (MazurProof.N13SpecialSmallFunctionCertificate.sixJetPolynomials a b i).coeff j = 0)
    (hcode : MazurProof.N13SpecialSmallFunctionCertificate.weightedJetCode a b = 0) : MazurProof.N13SpecialSixJetOrders.weightedLocalCode (MazurProof.N13SpecialSixJetOrders.function a b) = 0 := by
  exact MazurProof.N13SpecialSixJetOrders.weightedLocalCode_of_certified_jets a b hn hjets hcode

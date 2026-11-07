-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.centralV_norm_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T19:19:23.367507+00:00
-- url     : https://prove2.me/submissions/6480909c-0a5a-4069-8a73-1e481f37a88b

import Mathlib
import Definitions.Def_OAIQ098E125
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_abs_bound_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectminus_norm_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectplus_norm_e
import Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar
namespace IntegerIntervals

lemma precision_pos : (0:ℝ) < precision := by norm_num [precision]

end IntegerIntervals
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals
open scoped BigOperators

lemma column_bound_lt {n m : ℕ} {a : Matrix (Fin n) (Fin m) RBox}
    {A : Matrix (Fin n) (Fin m) ℝ} {u v : ℤ} (hv : 0 < v)
    (ha : ∀ i j, (a i j).Contains (A i j))
    (hc : ∀ j, (∑ i, (a i j).bound)*v < precision*u) :
    ∀ j, ∑ i, |A i j| < (u:ℝ)/v := by
  intro j
  have h₁ : (precision:ℝ)*(∑ i, |A i j|) ≤ (∑ i, ((a i j).bound:ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => RBox.abs_bound_e (ha i j)
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have h₂ : (∑ i, ((a i j).bound:ℝ))*(v:ℝ) < (precision:ℝ)*u := by
    exact_mod_cast hc j
  apply (mul_lt_mul_iff_right₀ precision_pos).mp
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hv').mpr
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h₁ hv'.le) h₂

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
open IntegerIntervals
open scoped BigOperators
lemma WplusBox_contains (i j : Fin 6) : (WplusBox i j).Contains (Wplus i j) := RBox.contains_rat_e _ _ (by norm_num)
lemma Wplus_column (j : Fin 6) : ∑ i, |Wplus i j| < (3084:ℝ)/100 := by
  apply column_bound_lt (u:=3084) (v:=100) (a:=WplusBox) (by norm_num) WplusBox_contains _ j
  intro k
  fin_cases k <;> decide +kernel
lemma WminusBox_contains (i j : Fin 6) : (WminusBox i j).Contains (Wminus i j) := RBox.contains_rat_e _ _ (by norm_num)
lemma Wminus_column (j : Fin 6) : ∑ i, |Wminus i j| < (183:ℝ)/100 := by
  apply column_bound_lt (u:=183) (v:=100) (a:=WminusBox) (by norm_num) WminusBox_contains _ j
  intro k
  fin_cases k <;> decide +kernel
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators

section
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

omit [DecidableEq ι] in
lemma matrixL1_apply (A : Matrix ι κ ℝ) (x : L1Finite κ) (i : ι) :
    matrixL1 A x i = ∑ j, A i j*x j := rfl

omit [DecidableEq ι] in
lemma matrixL1_norm_le {A : Matrix ι κ ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ j, ∑ i, |A i j| ≤ b) : ‖matrixL1 A‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro x
  rw [l1Finite_norm_e,l1Finite_norm_e,Finset.mul_sum]
  calc
    ∑ i, |matrixL1 A x i| ≤ ∑ i, ∑ j, |A i j| * |x j| := by
      apply Finset.sum_le_sum
      intro i _
      rw [matrixL1_apply]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => A i j*x j) Finset.univ
    _ = ∑ j, (∑ i, |A i j|)* |x j| := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ ≤ ∑ j, b* |x j| := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hA j) (abs_nonneg _)

omit [DecidableEq ι] in
lemma matrixL1_norm_lt [Nonempty κ] {A : Matrix ι κ ℝ} {b : ℝ}
    (hA : ∀ j, ∑ i, |A i j| < b) : ‖matrixL1 A‖ < b := by
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun j : κ => ∑ i, |A i j|) Finset.univ_nonempty
  exact (matrixL1_norm_le (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    (fun k => hj k (Finset.mem_univ _))).trans_lt (hA j)
end

section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma approximate_inverse_estimate (A W : E →L[ℝ] E) {δ : ℝ}
    (hd : δ < 1) (h : ‖1-W*A‖ ≤ δ) (x : E) :
    ‖x‖ ≤ ‖W (A x)‖/(1-δ) := by
  have he : x = W (A x)+(1-W*A) x := by simp
  have hx : ‖x‖ ≤ ‖W (A x)‖+δ*‖x‖ := calc
    _ = ‖W (A x)+(1-W*A) x‖ := congrArg norm he
    _ ≤ ‖W (A x)‖+‖(1-W*A) x‖ := norm_add_le _ _
    _ ≤ ‖W (A x)‖+δ*‖x‖ := add_le_add le_rfl ((1-W*A).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right h (norm_nonneg _)))
  apply (le_div_iff₀ (by linarith : 0 < 1-δ)).mpr
  nlinarith
end Inverse
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma certified_inverse_norm_le (A W : E →L[ℝ] E) {δ : ℝ}
    (hd : δ < 1) (h : ‖1-W*A‖ ≤ δ) :
    ‖(certifiedEquiv A W (h.trans_lt hd)).symm.toContinuousLinearMap‖ ≤ ‖W‖/(1-δ) := by
  have hd0 : 0 < 1-δ := sub_pos.mpr hd
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hd0.le)
  intro x
  have he : A ((certifiedEquiv A W (h.trans_lt hd)).symm x) = x :=
    (certifiedEquiv A W (h.trans_lt hd)).apply_symm_apply x
  calc
    ‖(certifiedEquiv A W (h.trans_lt hd)).symm x‖ ≤
        ‖W (A ((certifiedEquiv A W (h.trans_lt hd)).symm x))‖/(1-δ) :=
      approximate_inverse_estimate A W hd h _
    _ = ‖W x‖/(1-δ) := by rw [he]
    _ ≤ (‖W‖*‖x‖)/(1-δ) := div_le_div_of_nonneg_right (W.le_opNorm x) hd0.le
    _ = (‖W‖/(1-δ))*‖x‖ := by ring

end Inverse
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inverse bounds for the central interpolation block

Exact rational approximate inverses give bounds for the two central blocks.
-/

namespace SharpPlanar.Numerical
lemma Wplus_norm : ‖matrixL1 Wplus‖ < (3084:ℝ)/100 := matrixL1_norm_lt Wplus_column
lemma Wminus_norm : ‖matrixL1 Wminus‖ < (183:ℝ)/100 := matrixL1_norm_lt Wminus_column
lemma inversePlus_norm : ‖inversePlusEquiv.toContinuousLinearMap‖ < 32 := by
  have hh := certified_inverse_norm_le (matrixL1 Aplus) (matrixL1 Wplus)
    (by norm_num : (1:ℝ)/1000 < 1) defectplus_norm_e.le
  change ‖inversePlusEquiv.toContinuousLinearMap‖ ≤ _ at hh
  apply hh.trans_lt
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 1-1/1000)).mpr
  nlinarith [Wplus_norm]
lemma inverseMinus_norm : ‖inverseMinusEquiv.toContinuousLinearMap‖ < 32 := by
  have hh := certified_inverse_norm_le (matrixL1 Aminus) (matrixL1 Wminus)
    (by norm_num : (1:ℝ)/1000 < 1) defectminus_norm_e.le
  change ‖inverseMinusEquiv.toContinuousLinearMap‖ ≤ _ at hh
  apply hh.trans_lt
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 1-1/1000)).mpr
  nlinarith [Wminus_norm]
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite interpolation system

Schur complements give existence, uniqueness and norm bounds for the finite system.
-/

namespace SharpPlanar.Numerical
lemma centralV_norm_e_oai (neg : Bool) : ‖centralV neg‖ ≤ 32 := by
  cases neg
  · exact inversePlus_norm.le
  · exact inverseMinus_norm.le
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.centralV_norm_e_oai := @OAI.SharpPlanar.Numerical.centralV_norm_e_oai

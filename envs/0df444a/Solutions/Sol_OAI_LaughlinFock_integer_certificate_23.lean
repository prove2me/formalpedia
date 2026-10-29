-- Prove2me | solution 1 for OAI.LaughlinFock.integer_certificate_23
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:34:23.638808+00:00
-- url     : https://prove2.me/submissions/c7cb4927-0699-4816-82fb-d54311318a54

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L025
import Definitions.Def_OAIQ084L027
import Definitions.Def_OAIQ084L040
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_23_1
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_23_11
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_23_13
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_23_15
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_23_17
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_23_19
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_23_21
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_23_23
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_23_3
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_23_5
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_23_7
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_23_9
import Theorems.Thm_OAI_LaughlinFock_fourYChecked_23

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PolynomialPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial Positivity. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix ComplexOrder BigOperators
open Polynomial



theorem real_matrix_posSemidef_complex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosSemidef) :
    (M.map (algebraMap ℝ ℂ)).PosSemidef := by
  have hH : (M.map (algebraMap ℝ ℂ)).IsHermitian := by
    apply Matrix.IsHermitian.ext_iff.mpr
    intro i j
    have h := Matrix.IsHermitian.ext_iff.mp hM.isHermitian i j
    simpa using congrArg (algebraMap ℝ ℂ) h
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  have hRe := hM.dotProduct_mulVec_nonneg (fun i => (x i).re)
  have hIm := hM.dotProduct_mulVec_nonneg (fun i => (x i).im)
  apply Complex.nonneg_iff.mpr
  constructor
  · have he : (star x ⬝ᵥ (M.map (algebraMap ℝ ℂ) *ᵥ x)).re =
        (fun i => (x i).re) ⬝ᵥ (M *ᵥ fun i => (x i).re) +
        (fun i => (x i).im) ⬝ᵥ (M *ᵥ fun i => (x i).im) := by
      simp [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.sum_add_distrib,
        Complex.mul_re, Complex.mul_im, Finset.mul_sum]
    rw [he]
    simpa only [star_trivial, Pi.star_apply] using add_nonneg hRe hIm
  · exact (hH.im_star_dotProduct_mulVec_self x).symm



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_LDL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L D L. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem rational_ldl_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M L : Matrix ι ι ℚ) (d : ι → ℚ)
    (he : M = L * Matrix.diagonal d * Lᵀ) (hd : ∀ i, 0 ≤ d i) :
    (M.map (algebraMap ℚ ℂ)).PosSemidef := by
  let Lr := L.map (algebraMap ℚ ℝ)
  have hh : (Matrix.diagonal (fun i => (d i : ℝ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast hd i
  have hr : (M.map (algebraMap ℚ ℝ)).PosSemidef := by
    have ht : (Lᵀ).map (algebraMap ℚ ℝ) = Lrᴴ := by
      ext i j
      simp [Lr]
    rw [he, Matrix.map_mul, Matrix.map_mul, ht]
    have he' : (Matrix.diagonal d).map (algebraMap ℚ ℝ) =
        Matrix.diagonal (fun i => (d i : ℝ)) := by
      ext i j
      by_cases hij : i=j <;> simp [hij]
    rw [he']
    exact hh.mul_mul_conjTranspose_same Lr
  have hc := real_matrix_posSemidef_complex (M.map (algebraMap ℚ ℝ)) hr
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  simp

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FastCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem integerCoupling_fast (c : ℤ) (z k p : ℕ) :
    integerCoupling c z k p = fastIntegerCoupling c z k p := by
  simp only [integerCoupling, fastIntegerCoupling, Nat.choose_eq_fast_choose]

theorem integerCopyPolynomial_fast (D T r p j k : ℕ) :
    integerCopyPolynomial D T r p j k = fastIntegerCopyPolynomial D T r p j k := by
  simp only [integerCopyPolynomial, fastIntegerCopyPolynomial, integerCoupling_fast]
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate23Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate23 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_23 : highestFourOccupations 23 = {{0,1,2,21}, {0,1,3,20}, {0,1,4,19}, {0,1,5,18}, {0,1,6,17}, {0,1,7,16}, {0,1,8,15}, {0,1,9,14}, {0,1,10,13}, {0,1,11,12}, {0,2,3,19}, {0,2,4,18}, {0,2,5,17}, {0,2,6,16}, {0,2,7,15}, {0,2,8,14}, {0,2,9,13}, {0,2,10,12}, {0,3,4,17}, {0,3,5,16}, {0,3,6,15}, {0,3,7,14}, {0,3,8,13}, {0,3,9,12}, {0,3,10,11}, {0,4,5,15}, {0,4,6,14}, {0,4,7,13}, {0,4,8,12}, {0,4,9,11}, {0,5,6,13}, {0,5,7,12}, {0,5,8,11}, {0,5,9,10}, {0,6,7,11}, {0,6,8,10}, {0,7,8,9}, {1,2,3,18}, {1,2,4,17}, {1,2,5,16}, {1,2,6,15}, {1,2,7,14}, {1,2,8,13}, {1,2,9,12}, {1,2,10,11}, {1,3,4,16}, {1,3,5,15}, {1,3,6,14}, {1,3,7,13}, {1,3,8,12}, {1,3,9,11}, {1,4,5,14}, {1,4,6,13}, {1,4,7,12}, {1,4,8,11}, {1,4,9,10}, {1,5,6,12}, {1,5,7,11}, {1,5,8,10}, {1,6,7,10}, {1,6,8,9}, {2,3,4,15}, {2,3,5,14}, {2,3,6,13}, {2,3,7,12}, {2,3,8,11}, {2,3,9,10}, {2,4,5,13}, {2,4,6,12}, {2,4,7,11}, {2,4,8,10}, {2,5,6,11}, {2,5,7,10}, {2,5,8,9}, {2,6,7,9}, {3,4,5,12}, {3,4,6,11}, {3,4,7,10}, {3,4,8,9}, {3,5,6,10}, {3,5,7,9}, {3,6,7,8}, {4,5,6,9}, {4,5,7,8}} := by
  decide +kernel

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_GramCache
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram Cache. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem integerHighestEntry_kernel (D : ℕ) (r : CopyLabel D) (A : Occupation 24) :
    integerHighestEntry D r A = kernelHighestEntry D r A := by
  simp only [integerHighestEntry, kernelHighestEntry, integerHighestTerm, kernelHighestTerm,
    integerCopyPolynomial_fast]

theorem integerFourGram_cached (D : ℕ) (xs : List (Occupation 24 × List ℚ))
    (h : ∀ r A, A ∈ highestFourOccupations D →
      kernelHighestEntry D r A = highestLookup xs r.val.val A) :
    integerFourGram D = cachedFourGram D xs := by
  ext r s
  apply Finset.sum_congr rfl
  intro A hA
  rw [integerHighestEntry_kernel, integerHighestEntry_kernel, h r A hA, h s A hA]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate23
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate23. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourHighestChecked_23 : ∀ r : CopyLabel 23, ∀ A∈highestFourOccupations 23,
    kernelHighestEntry 23 r A = highestLookup fourHighestCache_23 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_23_1
  · exact fourHighestNumber_23_3
  · exact fourHighestNumber_23_5
  · exact fourHighestNumber_23_7
  · exact fourHighestNumber_23_9
  · exact fourHighestNumber_23_11
  · exact fourHighestNumber_23_13
  · exact fourHighestNumber_23_15
  · exact fourHighestNumber_23_17
  · exact fourHighestNumber_23_19
  · exact fourHighestNumber_23_21
  · exact fourHighestNumber_23_23

theorem fourZChecked_23 (r s : CopyLabel 23) :
    integerFourGram 23 r s = fourZData_23 r s := by
  rw [integerFourGram_cached 23 fourHighestCache_23 fourHighestChecked_23]
  have h : ∀ r s : CopyLabel 23, cachedFourGram 23 fourHighestCache_23 r s = fourZData_23 r s := by
    simp only [cachedFourGram, fourOccupations_23]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_23 :
    fourZData_23 * (Matrix.diagonal (fun r : CopyLabel 23 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 23 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 23 => rationalCopyDiagonal 23 r.val.val) *
        fourYData_23 * Matrix.diagonal (fun r : CopyLabel 23 => rationalCopyDiagonal 23 r.val.val)) *
      fourZData_23 = fourLData_23 * Matrix.diagonal fourPivotData_23 * (fourLData_23)ᵀ := by
  have h : ∀ r s : CopyLabel 23,
      (fourZData_23 * (Matrix.diagonal (fun r : CopyLabel 23 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 23 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 23 => rationalCopyDiagonal 23 r.val.val) *
          fourYData_23 * Matrix.diagonal (fun r : CopyLabel 23 => rationalCopyDiagonal 23 r.val.val)) *
        fourZData_23 : Matrix (CopyLabel 23) (CopyLabel 23) ℚ) r s =
      (fourLData_23 * Matrix.diagonal fourPivotData_23 * (fourLData_23)ᵀ : Matrix (CopyLabel 23) (CopyLabel 23) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_23 : ∀ r, 0 ≤ fourPivotData_23 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_23, copyDiagonalData]

theorem integer_certificate_23_oai :
    ((integerCompression 23).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_23) (fourPivotData_23) _ fourPivotChecked_23
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 23 = fourYData_23 from Matrix.ext fourYChecked_23,
    show integerFourGram 23 = fourZData_23 from Matrix.ext fourZChecked_23]
  exact fourLDLChecked_23

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.integer_certificate_23_oai := @OAI.LaughlinFock.integer_certificate_23_oai

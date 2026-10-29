-- Prove2me | solution 1 for OAI.LaughlinFock.integer_certificate_14
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:20:05.044591+00:00
-- url     : https://prove2.me/submissions/d7d9ec3b-aa44-41ff-9552-09729e00e34d

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L027
import Definitions.Def_OAIQ084L034
import Definitions.Def_OAIQ084L040
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourYChecked_14

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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate14Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate14 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_14 : highestFourOccupations 14 = {{0,1,2,12}, {0,1,3,11}, {0,1,4,10}, {0,1,5,9}, {0,1,6,8}, {0,2,3,10}, {0,2,4,9}, {0,2,5,8}, {0,2,6,7}, {0,3,4,8}, {0,3,5,7}, {0,4,5,6}, {1,2,3,9}, {1,2,4,8}, {1,2,5,7}, {1,3,4,7}, {1,3,5,6}, {2,3,4,6}} := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate14
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate14. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourHighestNumber_14_1 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 1 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_14_3 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 3 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_14_5 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 5 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_14_7 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 7 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_14_9 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 9 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_14_11 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 11 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_14_13 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨13,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 13 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_14 : ∀ r : CopyLabel 14, ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 r A = highestLookup fourHighestCache_14 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_14_1
  · exact fourHighestNumber_14_3
  · exact fourHighestNumber_14_5
  · exact fourHighestNumber_14_7
  · exact fourHighestNumber_14_9
  · exact fourHighestNumber_14_11
  · exact fourHighestNumber_14_13

theorem fourZChecked_14 (r s : CopyLabel 14) :
    integerFourGram 14 r s = fourZData_14 r s := by
  rw [integerFourGram_cached 14 fourHighestCache_14 fourHighestChecked_14]
  have h : ∀ r s : CopyLabel 14, cachedFourGram 14 fourHighestCache_14 r s = fourZData_14 r s := by
    simp only [cachedFourGram, fourOccupations_14]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_14 :
    fourZData_14 * (Matrix.diagonal (fun r : CopyLabel 14 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 14 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 14 => rationalCopyDiagonal 14 r.val.val) *
        fourYData_14 * Matrix.diagonal (fun r : CopyLabel 14 => rationalCopyDiagonal 14 r.val.val)) *
      fourZData_14 = fourLData_14 * Matrix.diagonal fourPivotData_14 * (fourLData_14)ᵀ := by
  have h : ∀ r s : CopyLabel 14,
      (fourZData_14 * (Matrix.diagonal (fun r : CopyLabel 14 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 14 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 14 => rationalCopyDiagonal 14 r.val.val) *
          fourYData_14 * Matrix.diagonal (fun r : CopyLabel 14 => rationalCopyDiagonal 14 r.val.val)) *
        fourZData_14 : Matrix (CopyLabel 14) (CopyLabel 14) ℚ) r s =
      (fourLData_14 * Matrix.diagonal fourPivotData_14 * (fourLData_14)ᵀ : Matrix (CopyLabel 14) (CopyLabel 14) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_14 : ∀ r, 0 ≤ fourPivotData_14 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_14, copyDiagonalData]

theorem integer_certificate_14_oai :
    ((integerCompression 14).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_14) (fourPivotData_14) _ fourPivotChecked_14
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 14 = fourYData_14 from Matrix.ext fourYChecked_14,
    show integerFourGram 14 = fourZData_14 from Matrix.ext fourZChecked_14]
  exact fourLDLChecked_14

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.integer_certificate_14_oai := @OAI.LaughlinFock.integer_certificate_14_oai

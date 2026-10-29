-- Prove2me | solution 1 for OAI.LaughlinFock.integer_certificate_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:36:32.552842+00:00
-- url     : https://prove2.me/submissions/77315a0c-b911-42e4-a987-f197b61145f1

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L026
import Definitions.Def_OAIQ084L038
import Definitions.Def_OAIQ084L041
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourYChecked_8

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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate08Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate08 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_8 : highestFourOccupations 8 = {{0,1,2,6}, {0,1,3,5}, {0,2,3,4}} := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate08
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate08. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourHighestNumber_8_1 : ∀ A∈highestFourOccupations 8,
    kernelHighestEntry 8 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_8 1 A := by
  rw [fourOccupations_8]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_8_3 : ∀ A∈highestFourOccupations 8,
    kernelHighestEntry 8 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_8 3 A := by
  rw [fourOccupations_8]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_8_5 : ∀ A∈highestFourOccupations 8,
    kernelHighestEntry 8 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_8 5 A := by
  rw [fourOccupations_8]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_8_7 : ∀ A∈highestFourOccupations 8,
    kernelHighestEntry 8 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_8 7 A := by
  rw [fourOccupations_8]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_8 : ∀ r : CopyLabel 8, ∀ A∈highestFourOccupations 8,
    kernelHighestEntry 8 r A = highestLookup fourHighestCache_8 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_8_1
  · exact fourHighestNumber_8_3
  · exact fourHighestNumber_8_5
  · exact fourHighestNumber_8_7

theorem fourZChecked_8 (r s : CopyLabel 8) :
    integerFourGram 8 r s = fourZData_8 r s := by
  rw [integerFourGram_cached 8 fourHighestCache_8 fourHighestChecked_8]
  have h : ∀ r s : CopyLabel 8, cachedFourGram 8 fourHighestCache_8 r s = fourZData_8 r s := by
    simp only [cachedFourGram, fourOccupations_8]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_8 :
    fourZData_8 * (Matrix.diagonal (fun r : CopyLabel 8 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 8 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 8 => rationalCopyDiagonal 8 r.val.val) *
        fourYData_8 * Matrix.diagonal (fun r : CopyLabel 8 => rationalCopyDiagonal 8 r.val.val)) *
      fourZData_8 = fourLData_8 * Matrix.diagonal fourPivotData_8 * (fourLData_8)ᵀ := by
  have h : ∀ r s : CopyLabel 8,
      (fourZData_8 * (Matrix.diagonal (fun r : CopyLabel 8 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 8 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 8 => rationalCopyDiagonal 8 r.val.val) *
          fourYData_8 * Matrix.diagonal (fun r : CopyLabel 8 => rationalCopyDiagonal 8 r.val.val)) *
        fourZData_8 : Matrix (CopyLabel 8) (CopyLabel 8) ℚ) r s =
      (fourLData_8 * Matrix.diagonal fourPivotData_8 * (fourLData_8)ᵀ : Matrix (CopyLabel 8) (CopyLabel 8) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_8 : ∀ r, 0 ≤ fourPivotData_8 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_8, copyDiagonalData]

theorem integer_certificate_8_oai :
    ((integerCompression 8).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_8) (fourPivotData_8) _ fourPivotChecked_8
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 8 = fourYData_8 from Matrix.ext fourYChecked_8,
    show integerFourGram 8 = fourZData_8 from Matrix.ext fourZChecked_8]
  exact fourLDLChecked_8

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.integer_certificate_8_oai := @OAI.LaughlinFock.integer_certificate_8_oai

-- Prove2me | solution 1 for OAI.LaughlinFock.integer_certificate_19
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:26:12.601242+00:00
-- url     : https://prove2.me/submissions/bd160f3d-8e79-4fa6-89b9-c936fabd79f2

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L029
import Definitions.Def_OAIQ084L040
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourYChecked_19

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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate19Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate19 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_19 : highestFourOccupations 19 = {{0,1,2,17}, {0,1,3,16}, {0,1,4,15}, {0,1,5,14}, {0,1,6,13}, {0,1,7,12}, {0,1,8,11}, {0,1,9,10}, {0,2,3,15}, {0,2,4,14}, {0,2,5,13}, {0,2,6,12}, {0,2,7,11}, {0,2,8,10}, {0,3,4,13}, {0,3,5,12}, {0,3,6,11}, {0,3,7,10}, {0,3,8,9}, {0,4,5,11}, {0,4,6,10}, {0,4,7,9}, {0,5,6,9}, {0,5,7,8}, {1,2,3,14}, {1,2,4,13}, {1,2,5,12}, {1,2,6,11}, {1,2,7,10}, {1,2,8,9}, {1,3,4,12}, {1,3,5,11}, {1,3,6,10}, {1,3,7,9}, {1,4,5,10}, {1,4,6,9}, {1,4,7,8}, {1,5,6,8}, {2,3,4,11}, {2,3,5,10}, {2,3,6,9}, {2,3,7,8}, {2,4,5,9}, {2,4,6,8}, {2,5,6,7}, {3,4,5,8}, {3,4,6,7}} := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate19
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate19. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourHighestNumber_19_1 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 1 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_3 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 3 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_5 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 5 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_7 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 7 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_9 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 9 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_11 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 11 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_13 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨13,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 13 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_15 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨15,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 15 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_17 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨17,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 17 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_19 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨19,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 19 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_19 : ∀ r : CopyLabel 19, ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 r A = highestLookup fourHighestCache_19 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_19_1
  · exact fourHighestNumber_19_3
  · exact fourHighestNumber_19_5
  · exact fourHighestNumber_19_7
  · exact fourHighestNumber_19_9
  · exact fourHighestNumber_19_11
  · exact fourHighestNumber_19_13
  · exact fourHighestNumber_19_15
  · exact fourHighestNumber_19_17
  · exact fourHighestNumber_19_19

theorem fourZChecked_19 (r s : CopyLabel 19) :
    integerFourGram 19 r s = fourZData_19 r s := by
  rw [integerFourGram_cached 19 fourHighestCache_19 fourHighestChecked_19]
  have h : ∀ r s : CopyLabel 19, cachedFourGram 19 fourHighestCache_19 r s = fourZData_19 r s := by
    simp only [cachedFourGram, fourOccupations_19]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_19 :
    fourZData_19 * (Matrix.diagonal (fun r : CopyLabel 19 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 19 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 19 => rationalCopyDiagonal 19 r.val.val) *
        fourYData_19 * Matrix.diagonal (fun r : CopyLabel 19 => rationalCopyDiagonal 19 r.val.val)) *
      fourZData_19 = fourLData_19 * Matrix.diagonal fourPivotData_19 * (fourLData_19)ᵀ := by
  have h : ∀ r s : CopyLabel 19,
      (fourZData_19 * (Matrix.diagonal (fun r : CopyLabel 19 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 19 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 19 => rationalCopyDiagonal 19 r.val.val) *
          fourYData_19 * Matrix.diagonal (fun r : CopyLabel 19 => rationalCopyDiagonal 19 r.val.val)) *
        fourZData_19 : Matrix (CopyLabel 19) (CopyLabel 19) ℚ) r s =
      (fourLData_19 * Matrix.diagonal fourPivotData_19 * (fourLData_19)ᵀ : Matrix (CopyLabel 19) (CopyLabel 19) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_19 : ∀ r, 0 ≤ fourPivotData_19 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_19, copyDiagonalData]

theorem integer_certificate_19_oai :
    ((integerCompression 19).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_19) (fourPivotData_19) _ fourPivotChecked_19
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 19 = fourYData_19 from Matrix.ext fourYChecked_19,
    show integerFourGram 19 = fourZData_19 from Matrix.ext fourZChecked_19]
  exact fourLDLChecked_19

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.integer_certificate_19_oai := @OAI.LaughlinFock.integer_certificate_19_oai

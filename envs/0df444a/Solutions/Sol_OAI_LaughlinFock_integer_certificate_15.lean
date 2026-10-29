-- Prove2me | solution 1 for OAI.LaughlinFock.integer_certificate_15
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:20:27.664974+00:00
-- url     : https://prove2.me/submissions/705d88dc-cdab-4588-aad3-dea3a55e47fc

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L025
import Definitions.Def_OAIQ084L029
import Definitions.Def_OAIQ084L040
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourYLower_15

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
-- module Solutions.OAIQ084_LF.LaughlinFock_RowTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



theorem rowFourLevel_symm {t : ℕ} (b c : RowEntry t) :
    rowFourLevel b c = rowFourLevel c b := by
  have hb := (rowEntry_bounds b).2.2.2
  have hc := (rowEntry_bounds c).2.2.2
  dsimp [rowFourLevel]
  omega

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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate15Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate15 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_15 : highestFourOccupations 15 = {{0,1,2,13}, {0,1,3,12}, {0,1,4,11}, {0,1,5,10}, {0,1,6,9}, {0,1,7,8}, {0,2,3,11}, {0,2,4,10}, {0,2,5,9}, {0,2,6,8}, {0,3,4,9}, {0,3,5,8}, {0,3,6,7}, {0,4,5,7}, {1,2,3,10}, {1,2,4,9}, {1,2,5,8}, {1,2,6,7}, {1,3,4,8}, {1,3,5,7}, {1,4,5,6}, {2,3,4,7}, {2,3,5,6}} := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_TraceSymmetry
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Symmetry. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem rationalFourFactor_symm {t : ℕ} (D : ℕ) (b c : RowEntry t) :
    rationalFourFactor D b c = rationalFourFactor D c b := by
  unfold rationalFourFactor
  rw [rowFourLevel_symm b c]
  ring

theorem integerFourTrace_symm (D t : ℕ) (a : RowEntry t → ℚ) (r s : CopyLabel D) :
    integerFourTrace D t a r s = integerFourTrace D t a s r := by
  unfold integerFourTrace
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [rowFourLevel_symm c b, rationalFourFactor_symm D c b]
  split_ifs <;> ring

theorem integerRowsFourTrace_symm (D : ℕ) (r s : CopyLabel D) :
    integerRowsFourTrace D r s = integerRowsFourTrace D s r := by
  unfold integerRowsFourTrace
  simp only [Matrix.sum_apply]
  exact Finset.sum_congr rfl (fun t _ => integerFourTrace_symm D t.val (certificateAlpha t) r s)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate15
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate15. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYChecked_15 (r s : CopyLabel 15) :
    integerRowsFourTrace 15 r s = fourYData_15 r s := by
  have hh : ∀ r s : CopyLabel 15, fourYData_15 r s = fourYData_15 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_15 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_15 s r (by omega), hh]

theorem fourHighestNumber_15_1 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 1 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_3 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 3 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_5 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 5 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_7 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 7 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_9 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 9 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_11 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 11 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_13 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨13,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 13 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_15 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨15,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 15 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_15 : ∀ r : CopyLabel 15, ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 r A = highestLookup fourHighestCache_15 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_15_1
  · exact fourHighestNumber_15_3
  · exact fourHighestNumber_15_5
  · exact fourHighestNumber_15_7
  · exact fourHighestNumber_15_9
  · exact fourHighestNumber_15_11
  · exact fourHighestNumber_15_13
  · exact fourHighestNumber_15_15

theorem fourZChecked_15 (r s : CopyLabel 15) :
    integerFourGram 15 r s = fourZData_15 r s := by
  rw [integerFourGram_cached 15 fourHighestCache_15 fourHighestChecked_15]
  have h : ∀ r s : CopyLabel 15, cachedFourGram 15 fourHighestCache_15 r s = fourZData_15 r s := by
    simp only [cachedFourGram, fourOccupations_15]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_15 :
    fourZData_15 * (Matrix.diagonal (fun r : CopyLabel 15 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 15 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 15 => rationalCopyDiagonal 15 r.val.val) *
        fourYData_15 * Matrix.diagonal (fun r : CopyLabel 15 => rationalCopyDiagonal 15 r.val.val)) *
      fourZData_15 = fourLData_15 * Matrix.diagonal fourPivotData_15 * (fourLData_15)ᵀ := by
  have h : ∀ r s : CopyLabel 15,
      (fourZData_15 * (Matrix.diagonal (fun r : CopyLabel 15 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 15 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 15 => rationalCopyDiagonal 15 r.val.val) *
          fourYData_15 * Matrix.diagonal (fun r : CopyLabel 15 => rationalCopyDiagonal 15 r.val.val)) *
        fourZData_15 : Matrix (CopyLabel 15) (CopyLabel 15) ℚ) r s =
      (fourLData_15 * Matrix.diagonal fourPivotData_15 * (fourLData_15)ᵀ : Matrix (CopyLabel 15) (CopyLabel 15) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_15 : ∀ r, 0 ≤ fourPivotData_15 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_15, copyDiagonalData]

theorem integer_certificate_15_oai :
    ((integerCompression 15).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_15) (fourPivotData_15) _ fourPivotChecked_15
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 15 = fourYData_15 from Matrix.ext fourYChecked_15,
    show integerFourGram 15 = fourZData_15 from Matrix.ext fourZChecked_15]
  exact fourLDLChecked_15

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.integer_certificate_15_oai := @OAI.LaughlinFock.integer_certificate_15_oai

-- Prove2me | solution 1 for OAI.LaughlinFock.integer_certificate_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:36:33.730989+00:00
-- url     : https://prove2.me/submissions/81067479-fee4-40b3-8971-0290945acac6

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L026
import Definitions.Def_OAIQ084L029
import Definitions.Def_OAIQ084L039
import Definitions.Def_OAIQ084L042
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourYLower_9

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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate09Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate09 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_9 : highestFourOccupations 9 = {{0,1,2,7}, {0,1,3,6}, {0,1,4,5}, {0,2,3,5}, {1,2,3,4}} := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate09
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate09. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYChecked_9 (r s : CopyLabel 9) :
    integerRowsFourTrace 9 r s = fourYData_9 r s := by
  have hh : ∀ r s : CopyLabel 9, fourYData_9 r s = fourYData_9 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_9 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_9 s r (by omega), hh]

theorem fourHighestNumber_9_1 : ∀ A∈highestFourOccupations 9,
    kernelHighestEntry 9 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_9 1 A := by
  rw [fourOccupations_9]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_9_3 : ∀ A∈highestFourOccupations 9,
    kernelHighestEntry 9 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_9 3 A := by
  rw [fourOccupations_9]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_9_5 : ∀ A∈highestFourOccupations 9,
    kernelHighestEntry 9 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_9 5 A := by
  rw [fourOccupations_9]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_9_7 : ∀ A∈highestFourOccupations 9,
    kernelHighestEntry 9 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_9 7 A := by
  rw [fourOccupations_9]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_9_9 : ∀ A∈highestFourOccupations 9,
    kernelHighestEntry 9 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_9 9 A := by
  rw [fourOccupations_9]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_9 : ∀ r : CopyLabel 9, ∀ A∈highestFourOccupations 9,
    kernelHighestEntry 9 r A = highestLookup fourHighestCache_9 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_9_1
  · exact fourHighestNumber_9_3
  · exact fourHighestNumber_9_5
  · exact fourHighestNumber_9_7
  · exact fourHighestNumber_9_9

theorem fourZChecked_9 (r s : CopyLabel 9) :
    integerFourGram 9 r s = fourZData_9 r s := by
  rw [integerFourGram_cached 9 fourHighestCache_9 fourHighestChecked_9]
  have h : ∀ r s : CopyLabel 9, cachedFourGram 9 fourHighestCache_9 r s = fourZData_9 r s := by
    simp only [cachedFourGram, fourOccupations_9]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_9 :
    fourZData_9 * (Matrix.diagonal (fun r : CopyLabel 9 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 9 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 9 => rationalCopyDiagonal 9 r.val.val) *
        fourYData_9 * Matrix.diagonal (fun r : CopyLabel 9 => rationalCopyDiagonal 9 r.val.val)) *
      fourZData_9 = fourLData_9 * Matrix.diagonal fourPivotData_9 * (fourLData_9)ᵀ := by
  have h : ∀ r s : CopyLabel 9,
      (fourZData_9 * (Matrix.diagonal (fun r : CopyLabel 9 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 9 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 9 => rationalCopyDiagonal 9 r.val.val) *
          fourYData_9 * Matrix.diagonal (fun r : CopyLabel 9 => rationalCopyDiagonal 9 r.val.val)) *
        fourZData_9 : Matrix (CopyLabel 9) (CopyLabel 9) ℚ) r s =
      (fourLData_9 * Matrix.diagonal fourPivotData_9 * (fourLData_9)ᵀ : Matrix (CopyLabel 9) (CopyLabel 9) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_9 : ∀ r, 0 ≤ fourPivotData_9 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_9, copyDiagonalData]

theorem integer_certificate_9_oai :
    ((integerCompression 9).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_9) (fourPivotData_9) _ fourPivotChecked_9
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 9 = fourYData_9 from Matrix.ext fourYChecked_9,
    show integerFourGram 9 = fourZData_9 from Matrix.ext fourZChecked_9]
  exact fourLDLChecked_9

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.integer_certificate_9_oai := @OAI.LaughlinFock.integer_certificate_9_oai

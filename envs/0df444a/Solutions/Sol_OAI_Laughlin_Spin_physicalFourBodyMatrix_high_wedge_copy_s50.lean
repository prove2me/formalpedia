-- Prove2me | solution 1 for OAI.Laughlin.Spin.physicalFourBodyMatrix_high_wedge_copy_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:41:31.173199+00:00
-- url     : https://prove2.me/submissions/90fb901f-26d2-4115-91da-c1f6bea893d4

import Mathlib
import Definitions.Def_OAIQ050L021

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem fourBodyCopy_coordinate (Q r D n : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (p : Fin ((2*Q-2)+1)) (i : WedgePairIndex Q) :
    fourBodyCopy Q r D hr hA hB n (p,i) =
      ∑ b : Fin (genericCoupledWeight Q Q r+1), pairCoupledWedge Q r hr b.val i *
        ((-1 : ℝ)^(D-r) * genericUnitDescendant (2*Q-2) (genericCoupledWeight Q Q r)
          (D-r) hA hB n (p,b)) := by
  simp only [fourBodyCopy,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,tensorPairInclusion,
    Matrix.kroneckerMap,Matrix.of_apply,Matrix.one_apply,ite_mul,
    one_mul,zero_mul,pairCoupledInclusion,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairCoupledWedge_off (Q r n : ℕ) (hr : r ≤ Q) (i : WedgePairIndex Q)
    (hi : i.val.1.val+i.val.2.val ≠ r+n) :
    pairCoupledWedge Q r hr n i = 0 := by
  simp only [pairCoupledWedge,tensorToWedgePair,pairCoupledTensor,Pi.smul_apply,smul_eq_mul,
    genericUnitDescendant_off Q Q r n hr hr i.val hi,mul_zero]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CoefficientNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem fourBodyCopy_off (Q r D n : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (p : Fin ((2*Q-2)+1)) (i : WedgePairIndex Q)
    (hi : p.val+i.val.1.val+i.val.2.val ≠ D+n) :
    fourBodyCopy Q r D hr hA hB n (p,i) = 0 := by
  rw [fourBodyCopy_coordinate]
  apply Finset.sum_eq_zero
  intro b hb
  by_cases hi' : i.val.1.val+i.val.2.val=r+b.val
  · rw [genericUnitDescendant_off _ _ _ _ hA hB (p,b) (by dsimp; omega),mul_zero,mul_zero]
  · rw [pairCoupledWedge_off Q r b.val hr i hi',zero_mul]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_ErrorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem source_rows_admissible : ∀ row ∈ Certificate.rows, ∀ e ∈ row.2.2,
    row.1 ≤ e.1+e.2.1 := by decide

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_SignedCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem fourBodyCopy_signed_off (Q r D n p j k : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hT : p+j+k ≠ D+n) :
    dotProduct (fourBodyCopy Q r D hr hA hB n) (fourSignedUnit Q p j k) = 0 := by
  have hz (j k : ℕ) (hT : p+j+k ≠ D+n) :
      dotProduct (fourBodyCopy Q r D hr hA hB n) (fourWedgeUnit Q p j k) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [fourWedgeUnit]
    split_ifs with he
    · rw [fourBodyCopy_off Q r D n hr hrD hA hB i.1 i.2 (by omega),zero_mul]
    · exact mul_zero _
  rw [fourSignedUnit,dotProduct_sub,hz j k hT,hz k j (by omega),sub_self]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem source_fourBody_rows_support : ∀ row ∈ Certificate.rows, ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
    e.1+e.2.1+(f.1+f.2.1-row.1) ≤ 23 := by decide

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem realOuter_mulVec_row {I : Type*} [Fintype I] (u v w : I → ℝ) (i : I) :
    (realOuter u v *ᵥ w) i = u i * dotProduct w v := by
  simp only [Matrix.mulVec,dotProduct,realOuter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem fourBodyTermMatrix_high_copy (Q r D t : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (e f : ℕ × ℕ × ℤ) (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1)
    (hT : e.1+e.2.1+(f.1+f.2.1-t) < D) :
    fourBodyTermMatrix Q t e f * fourBodyInclusion Q r D hr hA hB = 0 := by
  ext i n
  change (fourBodyTermMatrix Q t e f *ᵥ fourBodyCopy Q r D hr hA hB n.val) i=0
  rw [fourBodyTermMatrix,Matrix.smul_mulVec]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [realOuter_mulVec_row,fourBodyCopy_signed_off Q r D n.val f.1 f.2.1
    (e.1+e.2.1-t) hr hrD hA hB (by omega),mul_zero,mul_zero]

theorem list_sum_mul_zero {I J K : Type*} [Fintype J]
    (l : List (Matrix I J ℝ)) (W : Matrix J K ℝ) (h : ∀ M ∈ l, M*W=0) : l.sum*W=0 := by
  induction l with
  | nil => simp
  | cons M l ih =>
    rw [List.sum_cons,Matrix.add_mul,h M (by simp),ih (fun A hA => h A (by simp [hA])),zero_add]

theorem physicalFourBodyMatrix_high_copy (Q r D : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) (hD : 23 < D) :
    physicalFourBodyMatrix Q * fourBodyInclusion Q r D hr hA hB = 0 := by
  unfold physicalFourBodyMatrix
  apply list_sum_mul_zero
  intro M hM
  rcases List.mem_map.mp hM with ⟨row,hrow,rfl⟩
  apply list_sum_mul_zero
  intro A hA'
  rcases List.mem_map.mp hA' with ⟨e,he,rfl⟩
  apply list_sum_mul_zero
  intro B hB'
  rcases List.mem_map.mp hB' with ⟨f,hf,rfl⟩
  exact fourBodyTermMatrix_high_copy Q r D row.1 hr hrD hA hB e f
    (source_rows_admissible row hrow e he) (source_rows_admissible row hrow f hf)
    (by have := source_fourBody_rows_support row hrow e he f hf; omega)

theorem real_matrix_mul_zero_complex {I J K : Type*} [Fintype J]
    (A : Matrix I J ℝ) (B : Matrix J K ℝ) (h : A*B=0) :
    A.map Complex.ofReal * B.map Complex.ofReal=0 := by
  ext i k
  have he := congrArg Complex.ofReal (congrFun (congrFun h i) k)
  simpa only [Matrix.mul_apply,Matrix.map_apply,Complex.ofReal_sum,Complex.ofReal_mul,
    Matrix.zero_apply,Complex.ofReal_zero] using he

theorem physicalFourBodyMatrix_high_wedge_copy_s50_oai (Q r D : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) (hD : 23 < D) :
    (physicalFourBodyMatrix Q).map Complex.ofReal * fourWedgeInclusion Q r D hr hA hB = 0 :=
  real_matrix_mul_zero_complex _ _ (physicalFourBodyMatrix_high_copy Q r D hr hrD hA hB hD)

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.physicalFourBodyMatrix_high_wedge_copy_s50_oai := @OAI.Laughlin.Spin.physicalFourBodyMatrix_high_wedge_copy_s50_oai

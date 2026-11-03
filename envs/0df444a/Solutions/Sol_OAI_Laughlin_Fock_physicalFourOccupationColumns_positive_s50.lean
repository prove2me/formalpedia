-- Prove2me | solution 1 for OAI.Laughlin.Fock.physicalFourOccupationColumns_positive_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:20:53.232286+00:00
-- url     : https://prove2.me/submissions/a6a94160-cada-4fe4-8a46-72062456051a

import Mathlib
import Definitions.Def_OAIQ050L016
import Theorems.Thm_OAI_Laughlin_Fock_physicalWedgeColumns_gram_s50
import Theorems.Thm_OAI_Laughlin_Fock_source_physical_four_body_certificates_s50
import Theorems.Thm_OAI_Laughlin_Spin_source_fourBody_error_matrix_s50
import Theorems.Thm_OAI_Laughlin_matrix_physical_compression_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Symmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yEntry_swap (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (he : t ≤ e.1 + e.2.1) (hf : t ≤ f.1 + f.2.1) :
    yEntry D r s t e f = yEntry D s r t f e := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp at he hf
  have hT : q+l+(p+j-t) = p+j+(q+l-t) := by omega
  simp only [yEntry, hT, Nat.add_comm s r]
  split_ifs <;> ring_nf

private theorem sum_add {Element : Type*} (xs : List Element) (f g : Element → ℚ) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem sum_swap {Element : Type*} (xs ys : List Element)
    (f : Element → Element → ℚ) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, sum_add]

theorem yRow_swap (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (h : ∀ e ∈ row.2.2, row.1 ≤ e.1 + e.2.1) :
    yRow D r s row = yRow D s r row := by
  unfold yRow
  rw [sum_swap]
  congr 1
  apply List.map_congr_left
  intro f hf
  congr 1
  apply List.map_congr_left
  intro e he
  exact yEntry_swap D r s row.1 e f (h e he) (h f hf)

theorem rows_valid : ∀ row ∈ rows, ∀ e ∈ row.2.2, row.1 ≤ e.1 + e.2.1 := by
  decide +kernel

theorem Y_symm (D r s : ℕ) : Y D r s = Y D s r := by
  unfold Y
  congr 3
  apply List.map_congr_left
  intro row hr
  exact yRow_swap D r s row (rows_valid row hr)

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix

theorem physicalLimitError_eq (D : ℕ) : physicalLimitError D = Certificate.scaledError D := by
  ext i j
  exact Spin.source_fourBody_error_matrix_s50 D i j

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_RealComplexMatrixPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped Matrix BigOperators ComplexOrder
open Matrix

theorem real_complex_matrix_hermitian {I : Type*} (M : Matrix I I ℝ) (hM : M.IsHermitian) :
    (M.map Complex.ofReal).IsHermitian := by
  ext i j
  have h := congrFun (congrFun hM.eq i) j
  simpa [Matrix.conjTranspose_apply,Matrix.map_apply] using congrArg Complex.ofReal h

theorem real_complex_matrix_positive {I : Type*} [Fintype I]
    (M : Matrix I I ℝ) (hM : M.PosSemidef) : (M.map Complex.ofReal).PosSemidef := by
  have hh := real_complex_matrix_hermitian M hM.isHermitian
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro z
  apply Complex.nonneg_iff.mpr
  constructor
  · have hr := hM.dotProduct_mulVec_nonneg (fun i => (z i).re)
    have hi := hM.dotProduct_mulVec_nonneg (fun i => (z i).im)
    have he : (star z ⬝ᵥ ((M.map Complex.ofReal)*ᵥ z)).re =
        (star (fun i => (z i).re) ⬝ᵥ (M*ᵥ (fun i => (z i).re))) +
        (star (fun i => (z i).im) ⬝ᵥ (M*ᵥ (fun i => (z i).im))) := by
      simp [dotProduct,Matrix.mulVec,Complex.mul_re,Complex.mul_im,Complex.re_sum,
        Matrix.map_apply,
        Finset.mul_sum,Finset.sum_add_distrib,sub_eq_add_neg]
    rw [he]
    exact add_nonneg hr hi
  · exact (hh.im_star_dotProduct_mulVec_self z).symm

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_WedgeCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix Spin

theorem physicalLimitMiddle_hermitian (D : ℕ) : (physicalLimitMiddle D).IsHermitian := by
  apply real_complex_matrix_hermitian
  apply Matrix.IsHermitian.sub
  · simp [Certificate.certificateDiagonal,Matrix.IsHermitian]
  · rw [physicalLimitError_eq]
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial,Certificate.scaledError,
      Certificate.weightSqrtDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal,
      Matrix.map_apply,Certificate.errorRational,Rat.coe_castHom]
    rw [Certificate.Y_symm D (Certificate.copyLabel j) (Certificate.copyLabel i)]
    ring

theorem source_physical_wedge_compression (Q D : ℕ) (hQ : D+1 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    (physicalWedgeColumns Q D * physicalLimitMiddle D * (physicalWedgeColumns Q D)ᴴ).PosSemidef := by
  apply matrix_physical_compression_s50 _ _ (physicalLimitMiddle_hermitian D)
  rw [physicalWedgeColumns_gram_s50 Q D hQ]
  have h := real_complex_matrix_positive _ (source_physical_four_body_certificates_s50 Q D hQ hD₁ hD₂)
  have hm : ∀ A B : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ,
      (A*B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal := by
    intro A B
    ext i j
    simp [Matrix.mul_apply,Matrix.map_apply,Complex.ofReal_sum]
  simpa only [physicalLimitMiddle,hm] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_LimitPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix Spin

theorem physicalFourOccupationColumns_positive_s50_oai (Q D : ℕ) (hQ : D+1 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    (physicalFourOccupationColumns Q D * physicalLimitMiddle D *
      (physicalFourOccupationColumns Q D)ᴴ).PosSemidef := by
  have h := (source_physical_wedge_compression Q D hQ hD₁ hD₂).submatrix
    (fun A : FourOccupation Q D => A.val)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext A B
  simp [physicalFourOccupationColumns,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.submatrix_apply]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physicalFourOccupationColumns_positive_s50_oai := @OAI.Laughlin.Fock.physicalFourOccupationColumns_positive_s50_oai

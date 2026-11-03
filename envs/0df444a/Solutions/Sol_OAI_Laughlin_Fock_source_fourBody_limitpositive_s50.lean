-- Prove2me | solution 1 for OAI.Laughlin.Fock.source_fourBody_limitpositive_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:32:39.245205+00:00
-- url     : https://prove2.me/submissions/d9a63187-9858-48f4-944d-c74b2f018a77

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016
import Theorems.Thm_OAI_Laughlin_Fock_limitFourCopyEnd_matrix_expansion_s50
import Theorems.Thm_OAI_Laughlin_Fock_physicalFourOccupationColumns_positive_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_smul_left (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q (c • x) y = star c * occupationInner Q x y := by
  simp [occupationInner,star_mul,Finset.mul_sum,mul_comm,mul_left_comm]

theorem occupationInner_smul_right (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q x (c • y) = c * occupationInner Q x y := by
  simp [occupationInner,Finset.mul_sum,mul_left_comm]

theorem occupationInner_sum_left {I : Type*} (Q : ℕ) (s : Finset I)
    (x : I → Space Q) (y : Space Q) :
    occupationInner Q (∑ a ∈ s, x a) y = ∑ a ∈ s, occupationInner Q (x a) y := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,star_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem occupationInner_sum_right {I : Type*} (Q : ℕ) (s : Finset I)
    (x : Space Q) (y : I → Space Q) :
    occupationInner Q x (∑ a ∈ s, y a) = ∑ a ∈ s, occupationInner Q x (y a) := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_MatrixQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix

theorem occupation_matrix_quadratic_positive {I : Type*} [Fintype I]
    (Q : ℕ) (M : Matrix I I ℂ) (hM : M.PosSemidef) (v : I → Space Q) :
    0 ≤ (∑ i, ∑ j, M i j * occupationInner Q (v i) (v j)).re := by
  have he : (∑ i, ∑ j, M i j * occupationInner Q (v i) (v j)) =
      ∑ A : Finset (Fin (Q+1)), star (fun i => (occupationBasis Q).repr (v i) A) ⬝ᵥ
        (M*ᵥ (fun i => (occupationBasis Q).repr (v i) A)) := by
    simp only [occupationInner,dotProduct,Matrix.mulVec,Finset.mul_sum,Pi.star_apply]
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro A hA
    ring
  rw [he,Complex.re_sum]
  exact Finset.sum_nonneg (fun A hA => (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg _)).1)

theorem occupation_matrix_quadratic_factor {I J : Type*} [Fintype I] [Fintype J]
    (Q : ℕ) (W : Matrix J I ℂ) (C : Matrix I I ℂ) (v : J → Space Q) :
    (∑ i, ∑ j, C i j * occupationInner Q
      (∑ a, star (W a i) • v a) (∑ b, star (W b j) • v b)) =
      ∑ a, ∑ b, (W*C*Wᴴ) a b * occupationInner Q (v a) (v b) := by
  simp_rw [occupationInner_sum_left,occupationInner_smul_left,star_star,
    occupationInner_sum_right,occupationInner_smul_right]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.mul_sum,Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a ha
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b hb
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  ring

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

theorem source_fourBody_limitpositive_s50_oai (Q D : ℕ) (hQ : D+1 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) (x : Space Q) :
    0 ≤ (∑ i : Fin ((D+1)/2), ∑ j : Fin ((D+1)/2), physicalLimitMiddle D i j *
      occupationInner Q (limitFourCopyEnd Q (Certificate.copyLabel i) D x)
        (limitFourCopyEnd Q (Certificate.copyLabel j) D x)).re := by
  simp_rw [limitFourCopyEnd_matrix_expansion_s50]
  rw [occupation_matrix_quadratic_factor]
  exact occupation_matrix_quadratic_positive Q _
    (physicalFourOccupationColumns_positive_s50 Q D hQ hD₁ hD₂) _

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.source_fourBody_limitpositive_s50_oai := @OAI.Laughlin.Fock.source_fourBody_limitpositive_s50_oai

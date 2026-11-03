-- Prove2me | solution 1 for OAI.Laughlin.Fock.occupationQuadratic_factor_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T17:51:56.877358+00:00
-- url     : https://prove2.me/submissions/444205f0-287c-4006-ae1b-52e44b3279b0

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L012

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_CopyQuadraticMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Matrix

theorem occupationQuadratic_factor_s50_oai {I J : Type*} [Fintype I] [Fintype J]
    (Q : ℕ) (C : I → I → ℝ) (β : I → J → ℝ) (v : J → Space Q) :
    occupationQuadratic Q C (fun i => ∑ a, (β i a : ℂ) • v a) =
      occupationQuadratic Q (copyQuadraticMatrix C β) v := by
  let W : Matrix J I ℂ := fun a i => (β i a : ℂ)
  let C' : Matrix I I ℂ := fun i j => (C i j : ℂ)
  have hm (a b : J) : (W*C'*Wᴴ) a b = (copyQuadraticMatrix C β a b : ℂ) := by
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.sum_mul]
    simp only [W,C',Complex.star_def,Complex.conj_ofReal,copyQuadraticMatrix,Complex.ofReal_sum,Complex.ofReal_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    ring
  have h := occupation_matrix_quadratic_factor Q W C' v
  simp only [W,Complex.star_def,Complex.conj_ofReal,hm] at h
  exact congrArg Complex.re h

end Laughlin.Fock

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Laughlin.Fock.occupationQuadratic_factor_s50_oai.{u_1, u_2} := @OAI.Laughlin.Fock.occupationQuadratic_factor_s50_oai.{u_1, u_2}

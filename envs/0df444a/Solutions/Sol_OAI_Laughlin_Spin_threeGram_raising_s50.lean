-- Prove2me | solution 1 for OAI.Laughlin.Spin.threeGram_raising_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:43:42.163419+00:00
-- url     : https://prove2.me/submissions/b046d11e-3b4d-4520-8ef7-013d17520201

import Mathlib
import Definitions.Def_OAIQ050L018
import Definitions.Def_OAIQ050L019
import Theorems.Thm_OAI_Laughlin_Spin_pairInclusion_raising_s50
import Theorems.Thm_OAI_Laughlin_Spin_tripleInclusion_transpose_raising_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TripleLadderIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem tripleInclusion_raising (Q : ℕ) (hQ : 0 < Q) :
    tripleRaise Q * tripleInclusion Q = tripleInclusion Q * totalRaise (2*Q-2) Q := by
  rw [totalRaise_kronecker]
  unfold tripleRaise tripleInclusion
  simp only [Matrix.add_mul,Matrix.mul_add,← Matrix.mul_kronecker_mul,
    Matrix.mul_one,Matrix.one_mul,pairInclusion_raising_s50 Q hQ]

theorem swap23Matrix_mul (Q : ℕ) (M : Matrix (TripleIndex Q) (TripleIndex Q) ℝ)
    (i j : TripleIndex Q) : (swap23Matrix Q * M) i j = M (swap23 i) j := by
  simp [Matrix.mul_apply,swap23Matrix]

theorem mul_swap23Matrix (Q : ℕ) (M : Matrix (TripleIndex Q) (TripleIndex Q) ℝ)
    (i j : TripleIndex Q) : (M * swap23Matrix Q) i j = M i (swap23 j) := by
  have he (k : TripleIndex Q) : swap23 k=j ↔ k=swap23 j := by
    constructor
    · intro h; simpa using congrArg swap23 h
    · intro h; rw [h,swap23_involutive]
  simp [Matrix.mul_apply,swap23Matrix,he]

theorem swap23_raising (Q : ℕ) : swap23Matrix Q * tripleRaise Q = tripleRaise Q * swap23Matrix Q := by
  ext a b
  rw [swap23Matrix_mul,mul_swap23Matrix]
  rcases a with ⟨⟨i,j⟩,k⟩
  rcases b with ⟨⟨l,m⟩,n⟩
  simp only [tripleRaise,totalRaise,Matrix.add_apply,Matrix.kroneckerMap,
    Matrix.one_apply,Matrix.of_apply,swap23,Prod.mk.injEq]
  split_ifs <;> simp_all
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_SpinCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem swapCompression_raising (Q : ℕ) (hQ : 0 < Q) :
    swapCompression Q * totalRaise (2*Q-2) Q = totalRaise (2*Q-2) Q * swapCompression Q := by
  unfold swapCompression
  calc
    _ = (tripleInclusion Q)ᵀ * swap23Matrix Q *
      (tripleInclusion Q * totalRaise (2*Q-2) Q) := by simp only [Matrix.mul_assoc]
    _ = (tripleInclusion Q)ᵀ * swap23Matrix Q *
      (tripleRaise Q * tripleInclusion Q) := by rw [tripleInclusion_raising Q hQ]
    _ = (tripleInclusion Q)ᵀ * (swap23Matrix Q * tripleRaise Q) * tripleInclusion Q := by
      simp only [Matrix.mul_assoc]
    _ = (tripleInclusion Q)ᵀ * (tripleRaise Q * swap23Matrix Q) * tripleInclusion Q := by
      rw [swap23_raising]
    _ = ((tripleInclusion Q)ᵀ * tripleRaise Q) * swap23Matrix Q * tripleInclusion Q := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [tripleInclusion_transpose_raising_s50 Q hQ]; simp only [Matrix.mul_assoc]

theorem threeGram_raising_s50_oai (Q : ℕ) (hQ : 0 < Q) :
    threeGram Q * totalRaise (2*Q-2) Q = totalRaise (2*Q-2) Q * threeGram Q := by
  simp only [threeGram,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,
    Matrix.smul_mul,Matrix.mul_smul,swapCompression_raising Q hQ]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.threeGram_raising_s50_oai := @OAI.Laughlin.Spin.threeGram_raising_s50_oai

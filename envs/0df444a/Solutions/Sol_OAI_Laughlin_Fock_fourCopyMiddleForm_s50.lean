-- Prove2me | solution 1 for OAI.Laughlin.Fock.fourCopyMiddleForm_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:17:12.477651+00:00
-- url     : https://prove2.me/submissions/479cf829-9ef6-4b82-ac91-97f7d8c5cd54

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_FockHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_smul {I : Type*} [Fintype I] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (c : ℂ) (M : Matrix I I ℂ) (x : Space Q) :
    contractionForm Q minus (c • M) x = c * contractionForm Q minus M x := by
  simp only [contractionForm,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

theorem contractionForm_sum {I J : Type*} [Fintype I] [Fintype J] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (M : J → Matrix I I ℂ) (x : Space Q) :
    contractionForm Q minus (∑ j, M j) x = ∑ j, contractionForm Q minus (M j) x := by
  simp only [contractionForm,Matrix.sum_apply,Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CopyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem fourCopyOperator_diagonal (Q D : ℕ) (hQ : D+2 ≤ Q) (c : OddPairLabel D → ℝ) :
    fourCopyOperator Q D hQ (Matrix.diagonal c) = ∑ r,
      (c r : ℂ) • (retainedFourInclusion Q D hQ r * (retainedFourInclusion Q D hQ r)ᴴ) := by
  classical
  simp [fourCopyOperator,Matrix.diagonal_apply,apply_ite,ite_smul]

theorem fourCopyOperator_sub (Q D : ℕ) (hQ : D+2 ≤ Q)
    (C E : OddPairLabel D → OddPairLabel D → ℝ) :
    fourCopyOperator Q D hQ (C-E) = fourCopyOperator Q D hQ C-fourCopyOperator Q D hQ E := by
  simp only [fourCopyOperator,Pi.sub_apply,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]

theorem fourCopyOperator_middle (Q D : ℕ) (hQ : D+2 ≤ Q) (hD : 1 ≤ D) :
    fourCopyOperator Q D hQ (finiteFourMiddle Q D) =
      (fourDimensionRatio Q D : ℂ) •
        (retainedFourInclusion Q D hQ (firstOddPairLabel D hD) *
          (retainedFourInclusion Q D hQ (firstOddPairLabel D hD))ᴴ) +
      ((3/10^6 : ℝ) : ℂ) • (∑ r : OddPairLabel D,
        retainedFourInclusion Q D hQ r * (retainedFourInclusion Q D hQ r)ᴴ) -
      fourCopyOperator Q D hQ (fun r s => physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s)) := by
  classical
  unfold finiteFourMiddle
  erw [fourCopyOperator_sub,fourCopyOperator_diagonal]
  have he (r : OddPairLabel D) : Certificate.copyLabel r=1 ↔ r=firstOddPairLabel D hD := by
    dsimp [Certificate.copyLabel,firstOddPairLabel]
    constructor
    · intro h; apply Fin.ext; dsimp; omega
    · intro h; have := congrArg Fin.val h; dsimp at this; omega
  simp only [Complex.ofReal_add,add_smul,Finset.sum_add_distrib]
  simp_rw [he]
  simp only [apply_ite,Complex.ofReal_zero,ite_smul,zero_smul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,← Finset.smul_sum]
  rfl

theorem fourDimensionRatio_exact (Q D : ℕ) (hQ : D+2 ≤ Q) :
    fourDimensionRatio Q D =
      ((4*Q-1-2*D : ℕ) : ℝ)/((2*Q-2+1 : ℕ) : ℝ) := by
  unfold fourDimensionRatio
  congr 1
  · rw [Nat.cast_sub (by omega : 2*D ≤ 4*Q-1),Nat.cast_sub (by omega : 1 ≤ 4*Q)]
    push_cast
    ring
  · rw [Nat.cast_add,Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast
    ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_MiddleForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem contractionForm_add {I : Type*} [Fintype I] (Q : ℕ)
    (L : I → Module.End ℂ (Space Q)) (M N : Matrix I I ℂ) (x : Space Q) :
    contractionForm Q L (M+N) x = contractionForm Q L M x+contractionForm Q L N x := by
  simp only [contractionForm,Matrix.add_apply,add_mul,Finset.sum_add_distrib]

theorem contractionForm_sub {I : Type*} [Fintype I] (Q : ℕ)
    (L : I → Module.End ℂ (Space Q)) (M N : Matrix I I ℂ) (x : Space Q) :
    contractionForm Q L (M-N) x = contractionForm Q L M x-contractionForm Q L N x := by
  simp only [contractionForm,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

theorem fourCopyMiddleForm_s50_oai (Q D : ℕ) (hQ : D+2 ≤ Q) (hD : 1 ≤ D) (x : Space Q) :
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ (finiteFourMiddle Q D)) x).re =
    (contractionForm Q (sourceFourFamilyEnd Q)
      (retainedFourInclusion Q D hQ (firstOddPairLabel D hD) *
        (retainedFourInclusion Q D hQ (firstOddPairLabel D hD))ᴴ) x).re +
    (3/10^6 : ℝ) * (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (∑ r : OddPairLabel D, (contractionForm Q (sourceFourFamilyEnd Q)
        (retainedFourInclusion Q D hQ r*(retainedFourInclusion Q D hQ r)ᴴ) x).re) -
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (contractionForm Q (sourceFourFamilyEnd Q)
        (fourCopyOperator Q D hQ (fun r s => physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s))) x).re := by
  rw [fourCopyOperator_middle Q D hQ hD,contractionForm_sub,contractionForm_add]
  simp only [contractionForm_smul,contractionForm_sum,Complex.sub_re,Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.re_sum]
  rw [fourDimensionRatio_exact Q D hQ]
  have ha : ((2*Q-2+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd : ((4*Q-1-2*D : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 4*Q-1-2*D ≠ 0 by omega)
  field_simp

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.fourCopyMiddleForm_s50_oai := @OAI.Laughlin.Fock.fourCopyMiddleForm_s50_oai

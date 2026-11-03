-- Prove2me | solution 1 for OAI.Laughlin.Fock.source_rows_normal_two_three_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:53:12.151282+00:00
-- url     : https://prove2.me/submissions/db75494d-0517-4239-8b55-a3a9d7c4ba7e

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L020
import Theorems.Thm_OAI_Laughlin_Fock_row_normal_square_s50

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

theorem occupationInner_self (Q : ℕ) (x : Space Q) :
    occupationInner Q x x = (occupationNormSq Q x : ℂ) := by
  unfold occupationInner occupationNormSq
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
  rfl

end Laughlin.Fock

end OAI
end

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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_HighestFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_outer_cross {I : Type*} [Fintype I] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (v w : I → ℂ) (x : Space Q) :
    contractionForm Q minus (complexOuter v w) x =
      occupationInner Q (∑ i, star (v i) • minus i x) (∑ j, star (w j) • minus j x) := by
  simp only [occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,star_star,contractionForm,complexOuter,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Levels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem pairOrbitalUnit_family_sum (Q p j : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q)
    (v : PairOrbitalIndex Q → Space Q) :
    (∑ i, (pairOrbitalUnit Q p j i : ℂ) • v i) = v (⟨p,hp⟩,⟨j,by omega⟩) := by
  classical
  have he (i : PairOrbitalIndex Q) : (i.1.val=p ∧ i.2.val=j) ↔
      i=(⟨p,hp⟩,⟨j,by omega⟩) := by
    constructor
    · rintro ⟨h1,h2⟩; exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · intro h; subst i; exact ⟨rfl,rfl⟩
  simp only [pairOrbitalUnit,apply_ite,Complex.ofReal_one,Complex.ofReal_zero,
    ite_smul,one_smul,zero_smul,he]
  simp

theorem contractionForm_realOuter {I : Type*} [Fintype I] (Q : ℕ)
    (L : I → Module.End ℂ (Space Q)) (u v : I → ℝ) (x : Space Q) :
    contractionForm Q L ((realOuter u v).map Complex.ofReal) x =
      occupationInner Q (∑ i, (u i : ℂ) • L i x) (∑ j, (v j : ℂ) • L j x) := by
  have he : (realOuter u v).map Complex.ofReal =
      complexOuter (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) := by
    ext i j
    simp [realOuter,complexOuter]
  rw [he,contractionForm_outer_cross]
  simp only [Complex.star_def,Complex.conj_ofReal]

theorem threeBodyLevelMatrix_Fock (Q t T : ℕ) (ell : ℤ)
    (entries : List (ℕ × ℕ × ℤ)) (ht : t < 2*Q-2+1) (hT : T-t ≤ Q) (x : Space Q) :
    contractionForm Q (sourceThreeEnd Q)
      ((threeBodyLevelMatrix Q t T ell entries).map Complex.ofReal) x =
      ((ell : ℂ)/10^7) *
        (occupationInner Q (annihilate ⟨T-t,by omega⟩ (sourcePairEnd Q t x))
          (sourceRowLevel Q t T entries x) +
        occupationInner Q (sourceRowLevel Q t T entries x)
          (annihilate ⟨T-t,by omega⟩ (sourcePairEnd Q t x))) +
      (occupationNormSq Q (sourceRowLevel Q t T entries x) : ℂ) := by
  have hadd (M N : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
      (M+N).map Complex.ofReal = M.map Complex.ofReal + N.map Complex.ofReal := by
    ext i j; simp
  have hsmul (r : ℝ) (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
      (r • M).map Complex.ofReal = (r : ℂ) • M.map Complex.ofReal := by
    ext i j; simp
  simp only [threeBodyLevelMatrix,hadd,hsmul,contractionForm_add,contractionForm_smul,
    contractionForm_realOuter,pairOrbitalUnit_family_sum Q t (T-t) ht hT]
  simp only [sourceRowLevel,sourceThreeEnd,Module.End.mul_apply,occupationInner_self,
    Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat,
    Complex.ofReal_intCast]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Square
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem rowOutputMode_injective (Q t : ℕ) (hQ : 15 ≤ Q) :
    Function.Injective (rowOutputMode Q t hQ) := by
  intro T S h
  have he := congrArg Fin.val h
  dsimp [rowOutputMode] at he
  have hT := T.property
  have hS := S.property
  apply Subtype.ext
  apply Fin.ext
  omega

theorem sourceRowSquareVector_normal (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (ht : row.1 ≤ 7) (x : Space Q) :
    (occupationNormSq Q (sourceRowSquareVector Q hQ row x) : ℂ) =
      ((row.2.1 : ℂ)/10^7)^2 * (occupationNormSq Q (sourcePairEnd Q row.1 x) : ℂ) +
      (∑ T : RowLevel row.1, contractionForm Q (sourceThreeEnd Q)
        ((threeBodyLevelMatrix Q row.1 T.val.val row.2.1 row.2.2).map Complex.ofReal) x) +
      sourceRowFourForm Q hQ row x := by
  have h := row_normal_square_s50 Q (rowOutputMode Q row.1 hQ)
    (rowOutputMode_injective Q row.1 hQ) ((row.2.1 : ℝ)/10^7)
    (sourcePairEnd Q row.1 x) (fun T => sourceRowLevel Q row.1 T.val.val row.2.2 x)
  have hc : (((row.2.1 : ℝ)/10^7 : ℝ) : ℂ) = (row.2.1 : ℂ)/10^7 := by push_cast; rfl
  rw [hc] at h
  rw [sourceRowSquareVector,h]
  have hl (T : RowLevel row.1) := threeBodyLevelMatrix_Fock Q row.1 T.val.val
    row.2.1 row.2.2 (by omega) (by have hT := T.val.isLt; omega) x
  simp_rw [hl]
  simp only [sourceRowFourForm,rowOutputMode,Finset.sum_add_distrib]
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_SourceExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

 theorem source_threeBody_rows_support : ∀ row ∈ Certificate.rows,
    row.1 ≤ 7 ∧ ∀ e ∈ row.2.2, row.1 ≤ e.1+e.2.1 ∧ e.1+e.2.1 ≤ 15 ∧ e.1+e.2.1-row.1 ≤ 8 := by decide

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem contractionForm_list {I J : Type*} [Fintype I] (Q : ℕ)
    (L : I → Module.End ℂ (Space Q)) (l : List J) (M : J → Matrix I I ℂ) (x : Space Q) :
    contractionForm Q L (l.map M).sum x = (l.map (fun j => contractionForm Q L (M j) x)).sum := by
  induction l with
  | nil => simp [contractionForm]
  | cons j l ih => simp only [List.map_cons,List.sum_cons,contractionForm_add,ih]

theorem matrix_ofReal_list {I J : Type*} (l : List J) (M : J → Matrix I I ℝ) :
    ((l.map M).sum).map Complex.ofReal = (l.map (fun j => (M j).map Complex.ofReal)).sum := by
  induction l with
  | nil => ext i j; simp
  | cons k l ih =>
    simp only [List.map_cons,List.sum_cons]
    have he (A B : Matrix I I ℝ) : (A+B).map Complex.ofReal =
        A.map Complex.ofReal+B.map Complex.ofReal := by ext i j; simp
    rw [he,ih]

theorem physicalThreeBodyMatrix_row_sum (Q : ℕ) (x : Space Q) :
    contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal) x =
      (Certificate.rows.map (fun row => ∑ T : RowLevel row.1,
        contractionForm Q (sourceThreeEnd Q)
          ((threeBodyLevelMatrix Q row.1 T.val.val row.2.1 row.2.2).map Complex.ofReal) x)).sum := by
  simp only [physicalThreeBodyMatrix,matrix_ofReal_list,contractionForm_list]
  congr 1

theorem physicalPairRowMatrix_Fock (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (ht : row.1 ≤ 7) (x : Space Q) :
    contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
      (physicalPairRowMatrix Q row) x =
      ((row.2.1 : ℂ)/10^7)^2 * (occupationNormSq Q (sourcePairEnd Q row.1 x) : ℂ) := by
  let p : Fin (2*Q-2+1) := ⟨row.1,by omega⟩
  have he (i : Fin (2*Q-2+1)) : i.val=row.1 ↔ i=p := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; subst i; rfl
  simp only [contractionForm,physicalPairRowMatrix,he,ite_mul,zero_mul]
  simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,occupationInner_self]
  rfl

theorem source_rows_normal_two_three_s50_oai (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) :
    (Certificate.rows.map (fun row => (occupationNormSq Q (sourceRowSquareVector Q hQ row x) : ℂ))).sum =
      contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
        (physicalTwoBodyMatrix Q) x +
      contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal) x +
      (Certificate.rows.map (fun row => sourceRowFourForm Q hQ row x)).sum := by
  rw [physicalTwoBodyMatrix,contractionForm_list,physicalThreeBodyMatrix_row_sum]
  have hr (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hrow : row ∈ Certificate.rows) :
      (occupationNormSq Q (sourceRowSquareVector Q hQ row x) : ℂ) =
        contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
          (physicalPairRowMatrix Q row) x +
        (∑ T : RowLevel row.1, contractionForm Q (sourceThreeEnd Q)
          ((threeBodyLevelMatrix Q row.1 T.val.val row.2.1 row.2.2).map Complex.ofReal) x) +
        sourceRowFourForm Q hQ row x := by
    have ht := (source_threeBody_rows_support row hrow).1
    rw [sourceRowSquareVector_normal Q hQ row ht,physicalPairRowMatrix_Fock Q hQ row ht]
  rw [List.map_congr_left hr]
  simp only [List.sum_map_add]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.source_rows_normal_two_three_s50_oai := @OAI.Laughlin.Fock.source_rows_normal_two_three_s50_oai

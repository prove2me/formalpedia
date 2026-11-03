-- Prove2me | solution 1 for OAI.Laughlin.Fock.source_seven_squares_normal_form_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:53:14.422037+00:00
-- url     : https://prove2.me/submissions/5a5306da-721b-4670-8491-439c30e2435c

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L020
import Theorems.Thm_OAI_Laughlin_Fock_sourceRowFourEntry_physical_s50
import Theorems.Thm_OAI_Laughlin_Fock_source_rows_normal_two_three_s50

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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_SpinUnitary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators

theorem occupationInner_add_left (Q : ℕ) (x y z : Space Q) :
    occupationInner Q (x+y) z = occupationInner Q x z+occupationInner Q y z := by
  simp [occupationInner,add_mul,Finset.sum_add_distrib]

theorem occupationInner_add_right (Q : ℕ) (x y z : Space Q) :
    occupationInner Q x (y+z) = occupationInner Q x y+occupationInner Q x z := by
  simp [occupationInner,mul_add,Finset.sum_add_distrib]

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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Expansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem sourceRowLevel_entries (Q t T : ℕ) (entries : List (ℕ × ℕ × ℤ)) (x : Space Q) :
    sourceRowLevel Q t T entries x =
      (entries.map (fun e => if e.1+e.2.1=T then
        (sourceAlpha t e : ℂ) • sourceEntryThree Q e x else 0)).sum := by
  induction entries with
  | nil => simp [sourceRowLevel,threeBodyLevelVector]
  | cons e entries ih =>
    simp only [sourceRowLevel,threeBodyLevelVector,List.map_cons,List.sum_cons,
      Pi.add_apply,Complex.ofReal_add,add_smul,Finset.sum_add_distrib] at ih ⊢
    rw [ih]
    congr 1
    by_cases h : e.1+e.2.1=T
    · simp only [ite_eq_left h,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,sourceEntryThree,
        Finset.smul_sum,smul_smul]
    · simp [h]

theorem occupationInner_list_left {I : Type*} (Q : ℕ) (l : List I)
    (f : I → Space Q) (x : Space Q) :
    occupationInner Q (l.map f).sum x = (l.map (fun i => occupationInner Q (f i) x)).sum := by
  induction l with
  | nil => simp [occupationInner]
  | cons i l ih => simp only [List.map_cons,List.sum_cons,occupationInner_add_left,ih]

theorem occupationInner_list_right {I : Type*} (Q : ℕ) (l : List I)
    (f : I → Space Q) (x : Space Q) :
    occupationInner Q x (l.map f).sum = (l.map (fun i => occupationInner Q x (f i))).sum := by
  induction l with
  | nil => simp [occupationInner]
  | cons i l ih => simp only [List.map_cons,List.sum_cons,occupationInner_add_right,ih]

theorem finset_list_sum_swap {I J A : Type*} [AddCommMonoid A]
    (s : Finset I) (l : List J) (f : I → J → A) :
    (∑ i ∈ s, (l.map (f i)).sum) = (l.map (fun j => ∑ i ∈ s, f i j)).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

theorem rowLevel_sum_select {A : Type*} [AddCommMonoid A] (t n : ℕ)
    (ht : t ≤ n) (hn : n < 16) (f : RowLevel t → A) :
    (∑ T : RowLevel t, if n=T.val.val then f T else 0) = f ⟨⟨n,hn⟩,ht⟩ := by
  classical
  have he (T : RowLevel t) : n=T.val.val ↔ T=⟨⟨n,hn⟩,ht⟩ := by
    constructor
    · intro h; exact Subtype.ext (Fin.ext h.symm)
    · intro h; subst T; rfl
  simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Ungroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem boundedAnnihilate_rowOutput (Q t : ℕ) (hQ : 15 ≤ Q) (T : RowLevel t) :
    boundedAnnihilate Q (T.val.val-t) = annihilate (rowOutputMode Q t hQ T) := by
  have ht : T.val.val-t ≤ Q := by have h := T.val.isLt; omega
  rw [boundedAnnihilate,dite_eq_left ht]
  rfl

theorem linearMap_list_sum {I : Type*} (Q : ℕ) (L : Module.End ℂ (Space Q))
    (l : List I) (v : I → Space Q) :
    L (l.map v).sum = (l.map (fun i => L (v i))).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons,List.sum_cons,map_add,ih]

theorem sourceRowFourForm_entries (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hr : row ∈ Certificate.rows) (x : Space Q) :
    sourceRowFourForm Q hQ row x =
      (row.2.2.map (fun e => (row.2.2.map (fun f => sourceRowFourEntry Q row.1 e f x)).sum)).sum := by
  classical
  let term := fun (T S : RowLevel row.1) (e f : ℕ × ℕ × ℤ) =>
    if e.1+e.2.1=T.val.val then if f.1+f.2.1=S.val.val then
      -(sourceAlpha row.1 e : ℂ)*(sourceAlpha row.1 f : ℂ) * occupationInner Q
        (boundedAnnihilate Q (S.val.val-row.1) (sourceEntryThree Q e x))
        (boundedAnnihilate Q (T.val.val-row.1) (sourceEntryThree Q f x)) else 0 else 0
  have ht (T S : RowLevel row.1) :
      -occupationInner Q
        (annihilate (rowOutputMode Q row.1 hQ S) (sourceRowLevel Q row.1 T.val.val row.2.2 x))
        (annihilate (rowOutputMode Q row.1 hQ T) (sourceRowLevel Q row.1 S.val.val row.2.2 x)) =
      (row.2.2.map (fun e => (row.2.2.map (fun f => term T S e f)).sum)).sum := by
    rw [← boundedAnnihilate_rowOutput,← boundedAnnihilate_rowOutput]
    simp only [sourceRowLevel_entries,linearMap_list_sum]
    rw [occupationInner_list_left]
    simp_rw [occupationInner_list_right]
    rw [List.sum_neg]
    simp only [List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro e he
    rw [List.sum_neg]
    simp only [List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro f hf
    dsimp only [term]
    by_cases heT : e.1+e.2.1=T.val.val <;> by_cases hfS : f.1+f.2.1=S.val.val
    · simp only [ite_eq_left heT,ite_eq_left hfS,map_smul,occupationInner_smul_left,
        occupationInner_smul_right,Complex.star_def,Complex.conj_ofReal]
      ring
    all_goals simp [heT,hfS,occupationInner]
  rw [sourceRowFourForm,← Finset.sum_neg_distrib]
  simp only [← Finset.sum_neg_distrib,ht]
  simp_rw [finset_list_sum_swap]
  congr 1
  apply List.map_congr_left
  intro e he
  congr 1
  apply List.map_congr_left
  intro f hf
  obtain ⟨het,he15,he8⟩ := (source_threeBody_rows_support row hr).2 e he
  obtain ⟨hft,hf15,hf8⟩ := (source_threeBody_rows_support row hr).2 f hf
  simp only [term,Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [rowLevel_sum_select row.1 (e.1+e.2.1) het (by omega)]
  rw [rowLevel_sum_select row.1 (f.1+f.2.1) hft (by omega)]
  rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_NormalCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem source_rows_four_form (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    (Certificate.rows.map (fun row => sourceRowFourForm Q (by omega) row x)).sum =
      contractionForm Q (sourceFourFamilyEnd Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) x := by
  simp only [physicalFourBodyMatrix,matrix_ofReal_list,contractionForm_list]
  congr 1
  apply List.map_congr_left
  intro row hr
  rw [sourceRowFourForm_entries Q (by omega) row hr]
  congr 1
  apply List.map_congr_left
  intro e he
  congr 1
  apply List.map_congr_left
  intro f hf
  exact sourceRowFourEntry_physical_s50 Q hQ row hr e f he hf x

theorem source_seven_squares_normal_form_s50_oai (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    (Certificate.rows.map (fun row => (occupationNormSq Q
      (sourceRowSquareVector Q (by omega) row x) : ℂ))).sum =
      contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
        (physicalTwoBodyMatrix Q) x +
      contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal) x +
      contractionForm Q (sourceFourFamilyEnd Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) x := by
  rw [source_rows_normal_two_three_s50 Q (by omega),source_rows_four_form Q hQ]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.source_seven_squares_normal_form_s50_oai := @OAI.Laughlin.Fock.source_seven_squares_normal_form_s50_oai

-- Prove2me | solution 1 for OAI.Saxl.ThreeRow.sixSquare_columns
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:08:15.505495+00:00
-- url     : https://prove2.me/submissions/8a925334-116b-4a9e-88fb-4f5ca7071fd7

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_NoMixedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! No Mixed Columns. -/

section

noncomputable section
namespace Saxl.FlagColumns
open Columns

lemma wedge_apply_det {r d : ℕ} (N : ℕ → Fin d → ℂ) (w : Fin r → Fin d) :
    wedge r N w = (Matrix.of (fun i j : Fin r => N i.val (w j))).det := by
  classical
  simp only [wedge, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    pure, Matrix.det_apply', Matrix.of_apply, signC]
  rfl

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowColumns
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.ThreeRow
open FlagColumns Columns Balance

lemma restrict_square {n : ℕ} (v : WordSpace n 3) (w : Fin n → Fin 6) :
    restrictLetters pairLetters (wordTensor n 3 3 (v ⊗ₜ[ℂ] v)) w =
      v (fun i => (pairCoords (w i)).1) * v (fun i => (pairCoords (w i)).2) := by
  change wordTensor n 3 3 (v ⊗ₜ[ℂ] v) (pairLetters ∘ w) = _
  rw [wordTensor_tmul]
  have hleft : splitLeft (d:=3) (e:=3) (pairLetters ∘ w) =
      fun i => (pairCoords (w i)).1 := by
    funext i
    exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (pairCoords (w i)))
  have hright : splitRight (d:=3) (e:=3) (pairLetters ∘ w) =
      fun i => (pairCoords (w i)).2 := by
    funext i
    exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (pairCoords (w i)))
  rw [hleft,hright]

lemma perm_three_sum {R : Type*} [AddCommMonoid R] (f : Equiv.Perm (Fin 3) → R) :
    ∑ g, f g = f 1 + f (Equiv.swap 0 1) + f (Equiv.swap 0 2) +
      f (Equiv.swap 1 2) + f (Equiv.swap 0 1 * Equiv.swap 1 2) +
      f (Equiv.swap 1 2 * Equiv.swap 0 1) := by
  have h : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
        Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by decide +kernel
  rw [h]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  ac_rfl

lemma symmetricTriple_expansion : symmetricTriple =
    Pi.single ![4,5,1] 1 + Pi.single ![5,4,1] 1 + Pi.single ![1,5,4] 1 +
    Pi.single ![4,1,5] 1 + Pi.single ![5,1,4] 1 + Pi.single ![1,4,5] 1 := by
  rw [symmetricTriple,perm_three_sum]
  have h₀ : tripleColors ∘ (1 : Equiv.Perm (Fin 3)) = ![4,5,1] := rfl
  have h₁ : tripleColors ∘ Equiv.swap 0 1 = ![5,4,1] := by decide
  have h₂ : tripleColors ∘ Equiv.swap 0 2 = ![1,5,4] := by decide
  have h₃ : tripleColors ∘ Equiv.swap 1 2 = ![4,1,5] := by decide
  have h₄ : tripleColors ∘ ((Equiv.swap 0 1 * Equiv.swap 1 2) : Equiv.Perm (Fin 3)) = ![5,1,4] := by decide
  have h₅ : tripleColors ∘ ((Equiv.swap 1 2 * Equiv.swap 0 1) : Equiv.Perm (Fin 3)) = ![1,4,5] := by decide
  rw [h₀,h₁,h₂,h₃,h₄,h₅]

lemma sixSquare_apply {n : ℕ} (v : WordSpace n 3) (w : Fin n → Fin 6) :
    sixSquare v w =
      v (fun i => (pairCoords (w i)).1) * v (fun i => (pairCoords (w i)).2) :=
  restrict_square v w

lemma sixSquare_product {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a 3) (u : WordSpace b 3) :
    sixSquare (positionProduct e v u) = positionProduct e (sixSquare v) (sixSquare u) := by
  funext w
  simp only [sixSquare_apply, positionProduct]
  exact mul_mul_mul_comm _ _ _ _

lemma sixSquare_pair (w : Fin 2 → Fin 6) :
    sixSquare (wedge 2 (standard 3)) w = sixPairForm (w 0) (w 1) := by
  rw [sixSquare_apply,wedge_apply_det,wedge_apply_det]
  simp only [Matrix.det_fin_two,Matrix.of_apply]
  generalize w 0 = a
  generalize w 1 = b
  fin_cases a <;> fin_cases b <;> (first | (simp [standard,pairCoords,sixPairForm]; all_goals first | (norm_num [standard,pairCoords,sixPairForm]; done) | rfl | decide) | (norm_num [standard,pairCoords,sixPairForm]; done) | norm_num [standard,pairCoords,sixPairForm])

lemma word_three_eq_iff {d : ℕ} (w : Fin 3 → Fin d) (a b c : Fin d) :
    w = ![a,b,c] ↔ w 0 = a ∧ w 1 = b ∧ w 2 = c := by
  constructor
  · rintro rfl; exact ⟨rfl,rfl,rfl⟩
  · rintro ⟨ha,hb,hc⟩
    funext i
    fin_cases i <;> assumption

lemma sixSquare_triple (w : Fin 3 → Fin 6) :
    sixSquare (wedge 3 (standard 3)) w = -symmetricTriple w := by
  rw [sixSquare_apply,wedge_apply_det,wedge_apply_det,symmetricTriple_expansion]
  simp only [Matrix.det_fin_three,Matrix.of_apply,Pi.add_apply,Pi.single_apply,word_three_eq_iff]
  generalize w 0 = a
  generalize w 1 = b
  generalize w 2 = c
  fin_cases a <;> fin_cases b <;> fin_cases c <;> (first | (simp [standard,pairCoords,Fin.ext_iff]; all_goals first | (norm_num [standard,pairCoords,Fin.ext_iff]; done) | rfl | decide) | (norm_num [standard,pairCoords,Fin.ext_iff]; done) | norm_num [standard,pairCoords,Fin.ext_iff])

end Saxl.ThreeRow
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowLocal
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Local. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.ThreeRow
open FlagColumns Columns Balance

lemma sixSquare_twos (m : ℕ) :
    sixSquare (blocks (twos m) (standard 3)) = pairFormTensor (pairPositions m) sixPairForm := by
  induction m with
  | zero =>
    funext w
    change sixSquare (blocks [] (standard 3)) w = _
    erw [blocks_nil,sixSquare_apply]
    simp [pairFormTensor]
  | succ m ih =>
    change sixSquare (blocks (2 :: twos m) (standard 3)) = _
    rw [blocks_cons]
    erw [sixSquare_product,ih]
    funext w
    change sixSquare (wedge 2 (standard 3)) (leftWord finSumFinEquiv.symm w) *
      pairFormTensor (pairPositions m) sixPairForm (rightWord finSumFinEquiv.symm w) = _
    rw [sixSquare_pair]
    unfold pairFormTensor
    rw [Fin.prod_univ_succ]
    apply congrArg₂ (· * ·)
    · congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      congr 1 <;> apply congrArg w <;> apply Fin.ext <;> simp <;> omega

lemma sixSquare_one (w : Fin 1 → Fin 6) :
    sixSquare (wedge 1 (standard 3)) w = if w 0 = 0 then 1 else 0 := by
  rw [sixSquare_apply,wedge_apply_det,wedge_apply_det]
  simp only [Matrix.det_unique,Matrix.of_apply]
  generalize w 0 = a
  fin_cases a <;> (first | (simp [standard,pairCoords,Fin.ext_iff]; all_goals first | (norm_num [standard,pairCoords,Fin.ext_iff]; done) | rfl | decide) | (norm_num [standard,pairCoords,Fin.ext_iff]; done) | norm_num [standard,pairCoords,Fin.ext_iff])

lemma sixSquare_ones (s : ℕ) :
    sixSquare (blocks (ones s) (standard 3)) = Pi.single (fun _ => (0 : Fin 6)) 1 := by
  classical
  induction s with
  | zero =>
    funext w
    change sixSquare (blocks [] (standard 3)) w = _
    erw [blocks_nil,sixSquare_apply]
    have hw : w = fun _ => 0 := by ext i; exact Fin.elim0 i
    simp [hw]
  | succ s ih =>
    change sixSquare (blocks (1 :: ones s) (standard 3)) = _
    rw [blocks_cons]
    erw [sixSquare_product,ih,
      single_positionProduct finSumFinEquiv.symm (fun _ => 0)]
    congr 1
    funext w
    rw [sixSquare_one,Pi.single_apply]
    congr 1
    simp only [eq_iff_iff]
    constructor
    · intro h
      funext i
      have he : i = 0 := Subsingleton.elim _ _
      simpa [he,leftWord] using h
    · intro h
      exact congrFun h 0

lemma sixSquare_columns_oai (m s : ℕ) :
    sixSquare (blocks (columns m s) (standard 3)) =
      -generator (pairPositions m) (shortSplit m s) (tripleSplit m s) := by
  change sixSquare (blocks ((twos m ++ ones s) ++ [3]) (standard 3)) = _
  rw [blocks_append,blocks_append]
  erw [sixSquare_product,sixSquare_product,sixSquare_twos,sixSquare_ones]
  have hthree : sixSquare (blocks [3] (standard 3)) = -symmetricTriple := by
    rw [blocks_cons,blocks_nil]
    erw [sixSquare_product]
    funext w
    change sixSquare (wedge 3 (standard 3)) _ * sixSquare (fun _ => 1) _ = _
    erw [sixSquare_triple,sixSquare_apply]
    simp only [mul_one]
    congr 1
  rw [hthree]
  funext w
  change (_ * _) * (-symmetricTriple _) = -((_ * _) * symmetricTriple _)
  rw [mul_neg]
  congr 2
  apply congrArg₂ (· * ·)
  · rfl
  · simp only [Pi.single_apply]
    congr 1
    apply propext
    constructor
    · intro h
      funext i
      have hi := congrFun h (⟨i.val,by simp [ones]⟩ : Fin (ones s).sum)
      exact hi
    · intro h
      funext i
      have hi := congrFun h (⟨i.val,by simpa [ones] using i.isLt⟩ : Fin s)
      exact hi

end Saxl.ThreeRow
end
end

end OAI
end

theorem solution : type_of% @OAI.Saxl.ThreeRow.sixSquare_columns_oai := @OAI.Saxl.ThreeRow.sixSquare_columns_oai

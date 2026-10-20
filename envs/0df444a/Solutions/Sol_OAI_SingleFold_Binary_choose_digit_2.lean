-- Prove2me | solution 2 for OAI.SingleFold.Binary.choose_digit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:53:22.931093+00:00
-- url     : https://prove2.me/submissions/dbac5e53-dd85-4d20-a358-22d6181a648f

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Binary.lean:L74-L87
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Binary.choose_digit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary

-- ---- from OAI.NumberTheory.SingleFold.Binary ----
namespace OAI

namespace SingleFold.Binary

lemma ofDigits_digit {B : ℕ} (hB : 0<B) (l : List ℕ) (hl : ∀ a∈l, a<B) (i : ℕ) :
    Nat.ofDigits B l/B^i%B=l[i]?.getD 0 := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i hB l hl]
  have hd : ∀ a∈l.drop i,a<B := fun a ha => hl a (List.mem_of_mem_drop ha)
  have he : l[i]?=(l.drop i)[0]? := by simp
  rw [he]
  generalize l.drop i = v at *
  cases v with
  | nil => simp
  | cons a v =>
    simp only [Nat.ofDigits_cons, Nat.add_mul_mod_self_left, List.getElem?_cons_zero, Option.getD_some]
    exact Nat.mod_eq_of_lt (hd a List.mem_cons_self)

lemma ofDigits_map_range (B n : ℕ) (f : ℕ → ℕ) :
    Nat.ofDigits B ((List.range n).map f) = ∑ i∈Finset.range n, f i*B^i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,Nat.ofDigits_append]
    simp [ih,Finset.sum_range_succ, mul_comm]

lemma choose_digit {x y B : ℕ} (hxy : x≤y) (hB : 2^y<B) :
    (B+1)^y/B^x%B=y.choose x := by
  have hpos : 0<B := lt_of_lt_of_le (by positivity : 0<2^y) (Nat.le_of_lt hB)
  have hl : ∀ a∈(List.range (y+1)).map (Nat.choose y),a<B := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact lt_of_le_of_lt (Nat.choose_le_two_pow y i) hB
  have he : (B+1)^y=Nat.ofDigits B ((List.range (y+1)).map (Nat.choose y)) := by
    rw [ofDigits_map_range,add_pow]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_comm]
  rw [he,ofDigits_digit hpos _ hl]
  simp [show x<y+1 by omega]

end SingleFold.Binary

namespace SingleFold.Compiler.MapSF
end SingleFold.Compiler.MapSF

namespace SingleFold.Compiler.ScalarSF
variable {α : Type} {f g h : (α → ℕ) → ℕ}
end SingleFold.Compiler.ScalarSF

namespace SingleFold.Binary
open Compiler
end SingleFold.Binary

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Binary


theorem solution : type_of% @_root_.OAI.SingleFold.Binary.choose_digit := @_root_.OAI.SingleFold.Binary.choose_digit

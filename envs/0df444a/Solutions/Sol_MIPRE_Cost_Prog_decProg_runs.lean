-- Prove2me | solution 1 for MIPRE.Cost.Prog.decProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:49:37.897507+00:00
-- url     : https://prove2.me/submissions/b9364a65-eaa5-4c15-83d8-5238d58be52b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Numeric.lean (solution of MIPRE.Cost.Prog.decProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Theorems.Thm_MIPRE_Cost_Prog_decLoop_runs
import Theorems.Thm_MIPRE_Cost_Prog_revOntoProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost
theorem size_encode_replicate_true (j : ℕ) :
    (encode (List.replicate j true)).size = 4 * j + 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [List.replicate_succ, encode_bitStr_cons, Data.size_cons, Data.ofBool_true,
      Data.size_nil, ih]
    omega
end MIPRE.Cost

namespace MIPRE.Cost
theorem size_encode_replicate_false_append (j : ℕ) (rest : BitStr) :
    (encode (List.replicate j false ++ true :: rest)).size = 2 * j + (encode rest).size + 4 := by
  induction j with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, encode_bitStr_cons, Data.size_cons,
      Data.ofBool_true, Data.size_nil]
    omega
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, encode_bitStr_cons, Data.size_cons,
      Data.ofBool_false, Data.size_nil, ih]
    omega
end MIPRE.Cost

namespace MIPRE.Cost
theorem size_encode_false_cons_replicate_true (j : ℕ) :
    (encode (false :: List.replicate j true)).size = 4 * j + 3 := by
  simp only [encode_bitStr_cons, Data.size_cons, Data.ofBool_false, Data.size_nil,
    size_encode_replicate_true]
  omega
end MIPRE.Cost

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
theorem solution (j : ℕ) (rest : BitStr) :
    ∃ t ≤ (j + 2) * (10 * (2 * j + (encode rest).size + 4) + 60),
      decProg.Runs (encode (List.replicate j false ++ true :: rest))
        (encode (List.replicate j true ++ false :: rest)) t := by
  have hl : (encode (List.replicate j false ++ true :: rest)).size =
      2 * j + (encode rest).size + 4 :=
    size_encode_replicate_false_append j rest
  have hp : (encode (false :: List.replicate j true)).size = 4 * j + 3 :=
    size_encode_false_cons_replicate_true j
  -- phase 1, from the empty accumulator
  obtain ⟨t₁, ht₁, h₁⟩ := decLoop_runs j rest 0 [encode (List.replicate j false ++ true :: rest)]
    (4 * j + (encode rest).size + 5) (by omega)
  -- phase 2: reverse `false :: true^j` onto `rest`
  obtain ⟨t₂, ht₂, h₂⟩ := revOntoProg_runs ((false :: List.replicate j true).map Data.ofBool)
    (rest.map Data.ofBool)
    [Data.cons (encode (List.replicate j false ++ true :: rest)) .nil,
      encode (List.replicate j false ++ true :: rest)]
    (4 * j + 3 + (encode rest).size)
    (le_of_eq (by rw [← encode_bitStr_eq_list, ← encode_bitStr_eq_list, hp]))
  refine ⟨(encode (List.replicate j false ++ true :: rest)).size + 1 + 1 + 1 +
    (t₁ + t₂ + 1) + 1, ?_, ?_⟩
  · have hA : t₁ ≤ (j + 2) * (4 * j + (encode rest).size + 20) :=
      ht₁.trans (Nat.mul_le_mul (by omega) (by omega))
    have hB : t₂ ≤ (j + 2) * (4 * j + (encode rest).size + 15) :=
      ht₂.trans (le_of_eq (by simp only [List.length_map, List.length_cons,
        List.length_replicate]; ring))
    have hC : (j + 2) * (4 * j + (encode rest).size + 20) +
        (j + 2) * (4 * j + (encode rest).size + 15) +
        (j + 2) * (2 * j + (encode rest).size + 9) =
        (j + 2) * (10 * j + 3 * (encode rest).size + 44) := by ring
    have hD : (j + 2) * (10 * j + 3 * (encode rest).size + 44) ≤
        (j + 2) * (10 * (2 * j + (encode rest).size + 4) + 60) :=
      Nat.mul_le_mul_left _ (by omega)
    have hE : 2 * j + (encode rest).size + 9 ≤ (j + 2) * (2 * j + (encode rest).size + 9) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have hpre := Eval.cons
      (Eval.var_of_get (env := [encode (List.replicate j false ++ true :: rest)]) (i := 0)
        (v := encode (List.replicate j false ++ true :: rest)) (by simp))
      (Eval.nil [encode (List.replicate j false ++ true :: rest)])
    have h₁' : Eval (Data.cons (encode (List.replicate j false ++ true :: rest)) .nil ::
        [encode (List.replicate j false ++ true :: rest)]) (.loop decBody)
        (.cons (encode (false :: List.replicate j true)) (encode rest)) t₁ := by
      simpa using h₁
    have h₂' : Eval (Data.cons (encode (false :: List.replicate j true)) (encode rest) ::
        [Data.cons (encode (List.replicate j false ++ true :: rest)) .nil,
          encode (List.replicate j false ++ true :: rest)]) revOntoProg
        (encode (List.replicate j true ++ false :: rest)) t₂ := by
      simpa [encode_bitStr_eq_list, List.map_append, List.map_cons, List.map_replicate,
        List.reverse_cons, List.reverse_replicate] using h₂
    exact Eval.let_ hpre (Eval.let_ h₁' h₂')

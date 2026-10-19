-- Prove2me | solution 1 for MIPRE.SAT.Fml.exists_circuit
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:57.636409+00:00
-- url     : https://prove2.me/submissions/cd98b50c-d8f1-4252-9b4d-3bfcb804cef6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Table.lean (solution of MIPRE.SAT.Fml.exists_circuit);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_Table
import Theorems.Thm_MIPRE_SAT_Fml_eval_toCircuit
import Theorems.Thm_MIPRE_SAT_Fml_toCircuit_wellFormed

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.mono {n m : ℕ} (h : n ≤ m) {f : Fml} (hf : f.InputsLt n) : f.InputsLt m := by
  induction f with
  | inp _ => exact lt_of_lt_of_le hf h
  | const _ => trivial
  | and _ _ ihf ihg => exact ⟨ihf hf.1, ihg hf.2⟩
  | or _ _ ihf ihg => exact ⟨ihf hf.1, ihg hf.2⟩
  | not _ ihf => exact ihf hf
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem evalBits_toCircuit (n : ℕ) (f : Fml) (l : List Bool) :
    (f.toCircuit n).evalBits l = f.eval fun i => l.getD i false :=
  eval_toCircuit n f _
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
theorem eval_table : ∀ (N : ℕ) (f : (Fin N → Bool) → Bool) (x : ℕ → Bool),
    (table N f).eval x = f fun i => x i
  | 0, f, x => by
    simp only [table, eval]
    congr
    funext i
    exact i.elim0
  | N + 1, f, x => by
    simp only [table, eval, eval_table N]
    have hsnoc : ∀ b : Bool, x N = b →
        (Fin.snoc (fun i : Fin N => x i) b : Fin (N + 1) → Bool) = fun i : Fin (N + 1) => x i := by
      intro b hb
      funext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simp [Fin.snoc_castSucc]
      · simp [Fin.snoc_last, hb]
    cases hx : x N with
    | false => simp [hsnoc false hx]
    | true => simp [hsnoc true hx]
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
theorem table_inputsLt : ∀ (N : ℕ) (f : (Fin N → Bool) → Bool), (table N f).InputsLt N
  | 0, _ => trivial
  | N + 1, f => by
    refine ⟨⟨Nat.lt_succ_self N, (table_inputsLt N _).mono (Nat.le_succ N)⟩,
      Nat.lt_succ_self N, (table_inputsLt N _).mono (Nat.le_succ N)⟩
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
theorem size_table : ∀ (N : ℕ) (f : (Fin N → Bool) → Bool), (table N f).size + 6 ≤ 7 * 2 ^ N
  | 0, _ => by simp [table, size]
  | N + 1, f => by
    simp only [table, size]
    have h1 := size_table N fun x => f (Fin.snoc x true)
    have h2 := size_table N fun x => f (Fin.snoc x false)
    rw [Nat.pow_succ]
    omega
end
end MIPRE.SAT.Fml

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Fml
theorem _root_.solution (N : ℕ) (f : (Fin N → Bool) → Bool) :
    ∃ C : Circuit, C.WellFormed ∧ C.inputs = N ∧ C.size ≤ 7 * 2 ^ N ∧
      ∀ x : Fin N → Bool, C.evalBits (List.ofFn x) = f x := by
  refine ⟨(table N f).toCircuit N, toCircuit_wellFormed _ (table_inputsLt N f), rfl,
    by rw [toCircuit_size]; have := size_table N f; omega, fun x => ?_⟩
  rw [evalBits_toCircuit, eval_table]
  congr
  funext i
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt]
  rfl
end MIPRE.SAT.Fml

-- Prove2me | solution 1 for MIPRE.Cost.Data.primrec_decode_prod_nat
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:41:01.023037+00:00
-- url     : https://prove2.me/submissions/6a29c2f1-ee22-46b7-a15d-0bc0ab9c309a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Semidecide.lean (solution of MIPRE.Cost.Data.primrec_decode_prod_nat);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Serial

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Data
/-- Case analysis on `Data`, primitive recursively. -/
theorem primrec_ite_nil {α σ : Type*} [Primcodable α] [Primcodable σ] {f : α → Data}
    {g : α → σ} {h : α → Data → Data → σ} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec fun p : α × Data × Data => h p.1 p.2.1 p.2.2) :
    Primrec fun a => if f a = nil then g a else h a (left (f a)) (right (f a)) :=
  Primrec.ite (PrimrecRel.comp Primrec.eq hf (Primrec.const nil)) hg
    (hh.comp (Primrec.pair Primrec.id
      (Primrec.pair (primrec_left.comp hf) (primrec_right.comp hf))))
end MIPRE.Cost.Data

namespace MIPRE.Cost
/-- The decoding of a pair out of a `cons`, spelled out. -/
theorem Data.decode_prod_cons {α β : Type*} [SizedEncoding α] [SizedEncoding β] (a b : Data) :
    (decode (Data.cons a b) : Option (α × β)) =
      match (decode a : Option α), (decode b : Option β) with
      | some x, some y => some (x, y)
      | _, _ => none := rfl
end MIPRE.Cost

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Data
theorem _root_.solution :
    Primrec fun d : Data => (decode d : Option (BitStr × ℕ)) := by
  have hinner : Primrec₂ fun (p : Data × Data × Data) (x : BitStr) =>
      (decode p.2.2 : Option ℕ).map fun n => (x, n) :=
    Primrec.option_map
      (Data.primrec_decode_nat.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hh : Primrec fun p : Data × Data × Data =>
      (decode p.2.1 : Option BitStr).bind fun x =>
        (decode p.2.2 : Option ℕ).map fun n => (x, n) :=
    Primrec.option_bind (Data.primrec_decode_bitStr.comp (Primrec.fst.comp Primrec.snd)) hinner
  refine (Data.primrec_ite_nil (f := fun d : Data => d)
    (g := fun _ : Data => (none : Option (BitStr × ℕ)))
    (h := fun _ a b => (decode a : Option BitStr).bind fun x =>
      (decode b : Option ℕ).map fun n => (x, n))
    Primrec.id (Primrec.const none) hh).of_eq fun d => ?_
  cases d with
  | nil => rfl
  | cons a b =>
    rw [if_neg (show Data.cons a b ≠ Data.nil by simp), Data.decode_prod_cons,
      Data.left_cons, Data.right_cons]
    rcases ha : (decode a : Option BitStr) with _ | x
    · rfl
    · rcases hb : (decode b : Option ℕ) with _ | n <;> rfl
end MIPRE.Cost.Data

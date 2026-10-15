-- Prove2me | solution 1 for MIPRE.Cost.exists_compile
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:41:30.256021+00:00
-- url     : https://prove2.me/submissions/a9b87e18-e085-4c8d-bc33-29d683102d40

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/FromPartrec.lean (solution of MIPRE.Cost.exists_compile);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
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
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Theorems.Thm_MIPRE_Cost_Prog_ofCode_complete
import Theorems.Thm_MIPRE_Cost_Prog_ofCode_sound
import Theorems.Thm_MIPRE_Cost_Prog_ofCode_wellScoped
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_hardcode_time_rev

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost
open Polynomial
/-- The description of a hardcoded program, spelled out. -/
theorem toData_hardcode (p : Prog) (d : Data) :
    (hardcode p d).toData = .cons (.ofNat 4) (.cons (.cons (.ofNat 2)
      (.cons (.cons (.ofNat 6) d) (.cons .nil .nil))) p.toData) := rfl
end MIPRE.Cost

namespace MIPRE.Cost.Data
theorem primrec_cons : Primrec₂ Data.cons := by
  refine Primrec₂.encode_iff.1 ?_
  refine (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
    (Primrec.encode.comp Primrec.snd))).of_eq ?_
  rintro ⟨a, b⟩
  rfl
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem ofNat_eq_iterate (n : ℕ) : Data.ofNat n = (fun d => cons nil d)^[n] nil := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem primrec_ofNat : Primrec Data.ofNat := by
  have hh : Primrec₂ fun (_ : ℕ) (d : Data) => cons nil d :=
    primrec_cons.comp (Primrec.const nil) Primrec.snd
  exact (Primrec.nat_iterate Primrec.id (Primrec.const nil) hh).of_eq fun n =>
    (ofNat_eq_iterate n).symm
end MIPRE.Cost.Data

namespace MIPRE.Cost.Prog
open Turing.ToPartrec (Code)
/-- Halting of the translation of `c` on `encL v` is halting of `c` on `v`. -/
theorem ofCode_halts_iff (c : Code) (v : List ℕ) :
    Halts (ofCode c) (encL v) ↔ (c.eval v).Dom := by
  constructor
  · rintro ⟨r, t, h⟩
    obtain ⟨w, -, hw⟩ := ofCode_complete c v r t h
    exact Part.dom_iff_mem.2 ⟨w, hw⟩
  · intro h
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.1 h
    obtain ⟨t, ht⟩ := ofCode_sound c v w hw
    exact ⟨_, t, ht⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost
open Turing.ToPartrec (Code)
theorem partrec_univPart : Partrec univPart :=
  (Computable.ofOption Computable.decode).bind
    (Nat.Partrec.Code.eval_part.comp Computable.snd (Computable.const 0))
end MIPRE.Cost

namespace MIPRE.Cost
open Turing.ToPartrec (Code)
theorem univPart_encode (pc : Nat.Partrec.Code) : univPart (Encodable.encode pc) = pc.eval 0 := by
  simp [univPart]
end MIPRE.Cost

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Turing.ToPartrec (Code)
theorem solution :
    ∃ compile : Nat.Partrec.Code → Prog,
      Computable (fun pc => (encode (compile pc) : Data)) ∧
      ∀ pc : Nat.Partrec.Code, Halts (compile pc) .nil ↔ (pc.eval 0).Dom := by
  obtain ⟨cu, hcu⟩ := Turing.ToPartrec.Code.exists_code (n := 1)
    (f := fun v : List.Vector ℕ 1 => univPart v.head)
    (Nat.Partrec'.of_part (partrec_univPart.comp Computable.vector_head))
  have hcu' : ∀ n : ℕ, cu.eval [n] = (univPart n).map pure := fun n => hcu ⟨[n], rfl⟩
  refine ⟨fun pc => hardcode (Prog.ofCode cu) (Data.ofNat (Encodable.encode pc)), ?_, fun pc => ?_⟩
  · -- `toData (hardcode p d)` is a fixed tree around `d`
    have : Primrec fun pc : Nat.Partrec.Code =>
        Data.cons (.ofNat 4) (.cons (.cons (.ofNat 2) (.cons (.cons (.ofNat 6)
          (Data.ofNat (Encodable.encode pc))) (.cons .nil .nil))) (Prog.ofCode cu).toData) :=
      Data.primrec_cons.comp (Primrec.const _) (Data.primrec_cons.comp
        (Data.primrec_cons.comp (Primrec.const _) (Data.primrec_cons.comp
          (Data.primrec_cons.comp (Primrec.const _) (Data.primrec_ofNat.comp Primrec.encode))
          (Primrec.const _))) (Primrec.const _))
    exact this.to_comp.of_eq fun pc => (toData_hardcode _ _).symm
  · -- halting of the hardcoded translation is halting of `pc` on `0`
    have hdom : (cu.eval [Encodable.encode pc]).Dom ↔ (pc.eval 0).Dom := by
      rw [hcu', univPart_encode]
      exact Iff.rfl
    rw [← hdom, ← Prog.ofCode_halts_iff]
    constructor
    · rintro ⟨r, t, h⟩
      obtain ⟨t', -, h'⟩ := hardcode_time_rev (Prog.ofCode_wellScoped cu) h
      exact ⟨r, t', h'⟩
    · rintro ⟨r, t, h⟩
      exact ⟨r, _, hardcode_time (Prog.ofCode_wellScoped cu) h⟩

-- Prove2me | solution 1 for MIPRE.Cost.Prog.searchProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:03:20.09373+00:00
-- url     : https://prove2.me/submissions/45b45fe1-45cb-4cd3-b2a5-8cc595f3a200

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Compression.lean (solution of MIPRE.Cost.Prog.searchProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
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
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Compression
import Theorems.Thm_MIPRE_Cost_hardcode_time

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost
theorem encode_prod {α β : Type*} [SizedEncoding α] [SizedEncoding β] (a : α) (b : β) :
    encode (a, b) = .cons (encode a) (encode b) := rfl
end MIPRE.Cost

namespace MIPRE.Cost.Prog
open Polynomial
theorem searchProg_wellScoped {univ S : Prog} (hU : univ.WellScoped 1) (hS : S.WellScoped 1) :
    (searchProg univ S).WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, by omega, trivial, callVar_wellScoped (by omega) hU,
    ⟨show 0 < 6 by omega, show 2 < 6 by omega⟩, callVar_wellScoped (by omega) hS⟩
end MIPRE.Cost.Prog

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Polynomial
theorem solution (U : UniversalMachine) {S : Prog} (hS : S.WellScoped 1)
    {c' e : Prog} {m : ℕ} {x r : Data} {tx ts : ℕ}
    (hx : c'.Runs (encode (e, (m, m))) x tx) (hSr : S.Runs (.cons x (encode m)) r ts) :
    ∃ T, (hardcode (searchProg U.univ S) (encode ((c', (e, (m, m))), m))).Runs .nil r T := by
  obtain ⟨tU, -, hU⟩ := U.time_le c' (encode (e, (m, m))) x tx hx
  have s1 := callVar_eval
    (env := [encode (c', (e, (m, m))), encode m, encode ((c', (e, (m, m))), m), Data.nil,
      Data.cons (encode ((c', (e, (m, m))), m)) Data.nil])
    (i := 0) U.closed (v := .cons (encode c') (encode (e, (m, m)))) (by simp [encode_prod]) hU
  have s2 := callVar_eval
    (env := Data.cons x (encode m) :: x :: [encode (c', (e, (m, m))), encode m,
      encode ((c', (e, (m, m))), m), Data.nil, Data.cons (encode ((c', (e, (m, m))), m)) Data.nil])
    (i := 0) hS (v := .cons x (encode m)) (by simp) hSr
  have hrun : (searchProg U.univ S).Runs (.cons (encode ((c', (e, (m, m))), m)) .nil) r _ :=
    Eval.elim_cons (env := [Data.cons (encode ((c', (e, (m, m))), m)) Data.nil]) (i := 0)
      (n := .nil) (a := encode ((c', (e, (m, m))), m)) (b := .nil) (by simp)
      (Eval.elim_cons (i := 0) (n := .nil) (a := encode (c', (e, (m, m)))) (b := encode m)
        (by simp [encode_prod])
        (Eval.let_ s1 (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := x) (by simp))
          (Eval.var_of_get (i := 2) (v := encode m) (by simp))) s2)))
  exact ⟨_, hardcode_time (searchProg_wellScoped U.closed hS) hrun⟩

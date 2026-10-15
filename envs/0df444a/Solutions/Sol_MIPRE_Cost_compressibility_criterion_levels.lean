-- Prove2me | solution 1 for MIPRE.Cost.compressibility_criterion_levels
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:35:21.733025+00:00
-- url     : https://prove2.me/submissions/d4f36020-68ff-480c-b2d9-2b303792469a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Compression.lean (solution of MIPRE.Cost.compressibility_criterion_levels);
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
import Theorems.Thm_MIPRE_Cost_compressibility_criterion_nested

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution
    (A B : ℕ → Set BitStr) (n₀ : ℕ)
    (yYes : BitStr) (hyes : ∀ n, n₀ ≤ n → yYes ∈ A n)
    (yNo : BitStr) (hno : ∀ n, n₀ ≤ n → yNo ∈ B n)
    (S : Prog) (hSws : S.WellScoped 1)
    (hS : ∀ (x : BitStr) (n : ℕ), Halts S (encode (x, n)) ↔ x ∉ B n)
    (Compr : PolyTimeFun (Prog × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (x : BitStr) (n : ℕ), n₀ ≤ n → 2 * esize c ≤ n →
      IsSuccinctDesc c n x → x.length ≤ n + 1 →
        (x ∈ A (2 * n + 1) → Compr (c, n) ∈ A n) ∧ (x ∈ B (2 * n + 1) → Compr (c, n) ∈ B n)) :
    ∃ (g : PolyTimeFun Prog BitStr) (K : ℕ),
      ∀ e : Prog, n₀ ≤ 2 ^ (K + 1 + esize e) ∧
        (Halts e .nil → g e ∈ A (2 ^ (K + 1 + esize e))) ∧
        (¬ Halts e .nil → g e ∈ B (2 ^ (K + 1 + esize e))) :=
  compressibility_criterion_nested A B B n₀ (fun _ => subset_rfl) yYes hyes yNo hno S hSws hS
    Compr hCompr

-- Prove2me | solution 1 for MIPRE.Halting.decYes_runs_true_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:49:26.818992+00:00
-- url     : https://prove2.me/submissions/eed889df-b2e4-46aa-9f96-9c1f64cebcad

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Strings.lean (solution of MIPRE.Halting.decYes_runs_true_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
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
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Theorems.Thm_MIPRE_Cost_Eval_deterministic

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Halting
open Cost
/-- On an input with at least four nodes on its right spine — the shape of a well-formed tuple
`(n, x, y, a, b)` — `decYes` returns `encode true` exactly when the last two components are
both `nil`. -/
theorem decYes_run_deep (A B C D E : Data) :
    ∃ t ≤ 10, decYes.Runs (.cons A (.cons B (.cons C (.cons D E))))
      (if D = .nil ∧ E = .nil then encode true else .nil) t := by
  rcases D with _ | ⟨D₁, D₂⟩
  · rcases E with _ | ⟨E₁, E₂⟩
    · refine ⟨9, by omega, ?_⟩
      rw [if_pos ⟨rfl, rfl⟩]
      exact Eval.elim_cons rfl (Eval.elim_cons rfl (Eval.elim_cons rfl
        (Eval.elim_cons rfl (Eval.elim_nil rfl (Eval.elim_nil rfl (Eval.const _ _))))))
    · refine ⟨7, by omega, ?_⟩
      rw [if_neg (by simp)]
      exact Eval.elim_cons rfl (Eval.elim_cons rfl (Eval.elim_cons rfl
        (Eval.elim_cons rfl (Eval.elim_nil rfl (Eval.elim_cons rfl (Eval.nil _))))))
  · refine ⟨6, by omega, ?_⟩
    rw [if_neg (by simp)]
    exact Eval.elim_cons rfl (Eval.elim_cons rfl (Eval.elim_cons rfl
      (Eval.elim_cons rfl (Eval.elim_cons rfl (Eval.nil _)))))
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost
theorem _root_.solution (n : ℕ) (x y a b : BitStr) :
    (∃ t, decYes.Runs (encode (n, x, y, a, b)) (encode true) t) ↔ (a = [] ∧ b = []) := by
  have hin : (encode (n, x, y, a, b) : Data) =
      .cons (encode n) (.cons (encode x) (.cons (encode y) (.cons (encode a) (encode b)))) := rfl
  have henc : ∀ l : BitStr, (encode l : Data) = .nil ↔ l = [] := by
    intro l
    cases l with
    | nil => simp [encode_bitStr_nil]
    | cons c l => simp [encode_bitStr_cons]
  obtain ⟨t', -, h'⟩ := decYes_run_deep (encode n) (encode x) (encode y) (encode a) (encode b)
  rw [← hin] at h'
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨he, -⟩ := h'.deterministic h
    by_contra hc
    rw [if_neg (by rw [henc, henc]; exact hc)] at he
    exact absurd he.symm (by simp [encode_bool, Data.ofBool])
  · rintro ⟨ha, hb⟩
    rw [if_pos ⟨(henc a).2 ha, (henc b).2 hb⟩] at h'
    exact ⟨t', h'⟩
end MIPRE.Halting

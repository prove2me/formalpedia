-- Prove2me | solution 1 for MIPRE.Cost.Prog.polyBounded_wrapHeadZ
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:51:58.574184+00:00
-- url     : https://prove2.me/submissions/5964fa30-7565-4d25-bc4a-2dd79aa8b27b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/WrapperCost.lean (solution of MIPRE.Cost.Prog.polyBounded_wrapHeadZ);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
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
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost
open Polynomial
/-- The size of the binary encoding of `n` is polynomially bounded. -/
theorem polyBounded_esize_nat : PolyBounded fun n => esize n :=
  ((PolyBounded.size.const_mul 4).add_const 1).mono fun n => esize_nat_le n
end MIPRE.Cost

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Cost
open Data
variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ)
theorem _root_.solution {Cf : ℕ → ℕ} (hCf : PolyBounded Cf) (kf : ℕ)
    (hdim : PolyBounded S.dim) : PolyBounded fun n => wrapHeadZ U S Cf kf n := by
  set q : Data := encode CL.Sampler.Query.dimension with hq
  have h1 : PolyBounded fun _ : ℕ => esize S.prog := PolyBounded.const _
  have h2 : PolyBounded fun n : ℕ => esize n := polyBounded_esize_nat
  have h3 : PolyBounded fun _ : ℕ => q.size := PolyBounded.const _
  have h4 : PolyBounded fun n : ℕ => esize (S.dim n) := polyBounded_esize_nat.comp hdim
  have h5 : PolyBounded fun n : ℕ => Cf n * (q.size + 1) ^ kf :=
    hCf.mul (PolyBounded.const _)
  have h6 : PolyBounded fun n : ℕ =>
      U.bound.eval (esize S.prog + (esize n + q.size + 1) + Cf n * (q.size + 1) ^ kf) :=
    PolyBounded.eval _ (((h1.add (h2.add_const (q.size + 1))).add h5))
  have h7 : PolyBounded fun n : ℕ => (Nat.size (S.dim n) + 2) *
      ((S.dim n + 1) * (4 * S.dim n + 14) + 7 * esize (S.dim n) + 8 * S.dim n + 90) :=
    ((PolyBounded.size.comp hdim).add_const 2).mul
      ((((hdim.add_const 1).mul ((hdim.const_mul 4).add_const 14)).add
        (h4.const_mul 7)).add ((hdim.const_mul 8).add_const 90))
  exact ((((((h1.add h2).add h3).add h4).add h5).add h6).add h7).add_const 10
end MIPRE.Cost.Prog

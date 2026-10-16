-- Prove2me | solution 1 for MIPRE.Halting.esize_frozen_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:15:18.858389+00:00
-- url     : https://prove2.me/submissions/e61738a7-cb43-46e6-a74e-0194f10d9d82

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Compressor.lean (solution of MIPRE.Halting.esize_frozen_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
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
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
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
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
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
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor
import Theorems.Thm_MIPRE_Cost_Data_encode_natOf
import Theorems.Thm_MIPRE_Cost_Data_size_sum_stackStep_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Machine
open Prog
theorem size_left_le (d : Data) : d.left.size ≤ d.size := by cases d <;> simp; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem size_right_le (d : Data) : d.right.size ≤ d.size := by cases d <;> simp; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Data
/-- Normalization does not grow a datum: it is either the datum or `nil`. -/
theorem size_normBin_le (d : Data) : (normBin d).size ≤ d.size := by
  unfold normBin
  split
  · exact le_rfl
  · have := d.size_pos
    simp only [size_nil]
    omega
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
/-- So the whole run adds at most the length of the string. -/
theorem size_sum_stackRun_le (x : BitStr) (s : List Data) :
    ((stackRun x s).map size).sum ≤ (s.map size).sum + x.length := by
  induction x generalizing s with
  | nil => simp
  | cons bit x ih =>
    rw [stackRun_cons]
    have h1 := ih (stackStep s bit)
    have h2 := size_sum_stackStep_le s bit
    simp only [List.length_cons]
    omega
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
/-- **What a string of length `L` can parse to**: a datum of size at most `L`, or `nil` when
the run leaves the stack empty. -/
theorem size_parse_le (x : BitStr) : (parse x).size ≤ max 1 x.length := by
  have h := size_sum_stackRun_le x []
  simp only [List.map_nil, List.sum_nil, Nat.zero_add] at h
  unfold parse
  rcases hs : stackRun x [] with _ | ⟨d, t⟩
  · simp
  · rw [hs] at h
    simp only [List.map_cons, List.sum_cons] at h
    simp only [List.headD_cons]
    exact le_max_of_le_right (by omega)
end MIPRE.Cost.Data

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem decProgData_eq (x : BitStr) : decProgData G U x = encode ((Vof G U x).decider.prog) := by
  rw [decProgData, sampData_eq, Prog.ProgD.dWrapCore_eq]
  rfl
end MIPRE.Halting

namespace MIPRE.Cost.Prog.ProgD
open Cost
open Data
theorem dFreeze_eq (k : ℕ) (p : Prog) :
    dFreeze (encode k) (encode p) = encode (Prog.freezeProg k p) := rfl
end MIPRE.Cost.Prog.ProgD

namespace MIPRE.Cost.Prog.ProgD
open Cost
open Data
theorem size_dFreeze (kD p : Data) : (dFreeze kD p).size = p.size + kD.size + 53 := by
  simp only [dFreeze, size_dL, size_dE, size_dC, size_dK, size_dV, size_dNil]
  omega
end MIPRE.Cost.Prog.ProgD

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem encode_frozen_sampler (x : BitStr) (n : ℕ) :
    (encode (frozen G U x n).sampler.prog : Data) = dFreeze (kD n) (sampD G x) := by
  show encode (Prog.freezeProg (2 * n + 1) (G.sampler (descLam x)).prog) = _
  rw [← dFreeze_eq, Cost.encode_two_mul_add_one, ← G.samplerProg_eq]
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem encode_frozen_decider (x : BitStr) (n : ℕ) :
    (encode (frozen G U x n).decider.prog : Data) = dFreeze (kD n) (wD G U x) := by
  show encode (Prog.freezeProg (2 * n + 1) (Vof G U x).decider.prog) = _
  rw [← dFreeze_eq, Cost.encode_two_mul_add_one, ← decProgData_eq]
  rfl
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- The parameter a string of length `L` denotes has an encoding of size at most `L + 1`. -/
theorem esize_descLam_le (x : BitStr) : esize (descLam x) ≤ x.length + 1 := by
  have hdl : esize (descLam x) = (Data.parse x).left.normBin.size := by
    show (encode (Data.natOf (Data.parse x).left) : Data).size = _
    rw [Data.encode_natOf]
  have hp : (Data.parse x).size ≤ x.length + 1 := (Data.size_parse_le x).trans (by omega)
  have hpl : (Data.parse x).left.size ≤ (Data.parse x).size := Machine.size_left_le _
  have hnb : (Data.parse x).left.normBin.size ≤ (Data.parse x).left.size := Data.size_normBin_le _
  omega
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- The sizes of the stages' values, against their bounds. -/
theorem size_sampD_le (x : BitStr) : (sampD G x).size ≤ sampBound G x.length :=
  (G.samplerProg.esize_apply_le (descLam x)).trans
    (polynomial_eval_mono _ (esize_descLam_le x))
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem size_wD_le (x : BitStr) : (wD G U x).size ≤ wBound G U x.length := by
  have hp : (Data.parse x).size ≤ x.length + 1 := (Data.size_parse_le x).trans (by omega)
  have hpr : (Data.parse x).right.size ≤ (Data.parse x).size := Machine.size_right_le _
  have hsamp := size_sampD_le G x
  have hu : (encode U.univ : Data).size = esize U.univ := rfl
  rw [wD, size_dWrapCore, hu, wBound]; omega
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem size_kD_le (n : ℕ) : (kD n).size ≤ kBound n := by
  have hn : (encode n : Data).size ≤ 4 * Nat.size n + 1 := esize_nat_le n
  show (Data.cons (Data.cons .nil .nil) (encode n)).size ≤ _
  simp only [Data.size_cons, Data.size_nil, kBound]; omega
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem _root_.solution (x : BitStr) (n : ℕ) :
    esize (frozen G U x n).sampler.prog + esize (frozen G U x n).decider.prog ≤
      fBound G U x.length n := by
  have e1 : esize (frozen G U x n).sampler.prog = (dFreeze (kD n) (sampD G x)).size := by
    show (encode _ : Data).size = _
    rw [encode_frozen_sampler]
  have e2 : esize (frozen G U x n).decider.prog = (dFreeze (kD n) (wD G U x)).size := by
    show (encode _ : Data).size = _
    rw [encode_frozen_decider]
  rw [e1, e2, size_dFreeze, size_dFreeze, fBound]
  have := size_sampD_le G x
  have := size_wD_le G U x
  have := size_kD_le n
  omega
end MIPRE.Halting

-- Prove2me | solution 1 for MIPRE.Halting.exists_ansBound_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:30:33.40799+00:00
-- url     : https://prove2.me/submissions/a1e0ec98-3794-4921-9cd2-656ce8c1db7b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Instantiation.lean (solution of MIPRE.Halting.exists_ansBound_le);
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
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Theorems.Thm_MIPRE_Cost_Data_encode_natOf
import Theorems.Thm_MIPRE_Cost_Data_size_sum_stackStep_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Machine
open Prog
theorem size_left_le (d : Data) : d.left.size ≤ d.size := by cases d <;> simp; omega
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
/-- **A datum denotes a number smaller than `2` to its size.** Through
`encode_natOf`, the normalized datum *is* the binary encoding of the number it denotes, so
the number has at most `d.size` binary digits. -/
theorem natOf_lt (d : Data) : natOf d < 2 ^ d.size := by
  refine lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) ?_)
  calc Nat.size (natOf d) ≤ esize (natOf d) := size_le_esize_nat _
    _ = (normBin d).size := by
        show (encode (natOf d) : Data).size = _
        rw [encode_natOf]
    _ ≤ d.size := size_normBin_le d
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
/-- **A string denotes a parameter exponential in its length at worst.** The parameter is the
number the left component of the parsed datum denotes, and parsing a string of length `L`
yields a datum of size at most `L` (`Data.size_parse_le`), which denotes a number below
`2 ^ L` (`Data.natOf_lt`). -/
theorem descLam_lt (x : BitStr) : descLam x < 2 ^ max 1 x.length :=
  lt_of_lt_of_le (Data.natOf_lt _)
    (Nat.pow_le_pow_right (by norm_num)
      ((Machine.size_left_le _).trans (Data.size_parse_le x)))
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
/-- The form the criterion's length bound is used in: `compr_spec`'s hypothesis
`x.length ≤ n + 1` caps the denoted parameter at `2 ^ (n + 1)`. -/
theorem descLam_lt_of_length_le {x : BitStr} {n : ℕ} (h : x.length ≤ n + 1) :
    descLam x < 2 ^ (n + 1) :=
  lt_of_lt_of_le (descLam_lt x) (Nat.pow_le_pow_right (by norm_num) (by omega))
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem _root_.solution (G : GapCompression) :
    ∃ lam₀ n₀ : ℕ, ∀ (x : BitStr) (lam n : ℕ), lam₀ ≤ lam → n₀ ≤ n → x.length ≤ n + 1 →
      ansBound G x (2 * n + 1) ≤ (2 ^ n) ^ lam := by
  obtain ⟨D, hD⟩ : ∃ D, D = G.bound.natDegree := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ i ∈ Finset.range (G.bound.natDegree + 1), G.bound.coeff i :=
    ⟨_, rfl⟩
  have hQ : ∀ y, 1 ≤ y → G.bound.eval y ≤ A * y ^ D := fun y hy => by
    rw [hA, hD]; exact polynomial_eval_le_sum_coeff_mul_pow G.bound hy
  refine ⟨2 * D + 1, Nat.size A + 2 * D + 1, fun x lam n hlam hn hx => ?_⟩
  have hdl : descLam x < 2 ^ (n + 1) := descLam_lt_of_length_le hx
  have h1 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  have h3 : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
  have hm : 2 * n + 1 + descLam x ≤ 2 ^ (n + 2) := by omega
  have hev : G.bound.eval (2 * n + 1 + descLam x) ≤ A * (2 ^ (n + 2)) ^ D :=
    (polynomial_eval_mono G.bound hm).trans (hQ _ Nat.one_le_two_pow)
  have key : Nat.size A + (n + 2) * D ≤ n * lam := by
    have h : Nat.size A + 2 * D ≤ n := by omega
    have e1 : Nat.size A + (n + 2) * D = Nat.size A + 2 * D + n * D := by ring
    have e2 : n * (2 * D + 1) = n + (n * D + n * D) := by ring
    refine le_trans ?_ (Nat.mul_le_mul_left n hlam)
    rw [e1, e2]
    exact Nat.add_le_add h (Nat.le_add_right _ _)
  calc ansBound G x (2 * n + 1) ≤ A * (2 ^ (n + 2)) ^ D := hev
    _ ≤ 2 ^ Nat.size A * (2 ^ (n + 2)) ^ D :=
        Nat.mul_le_mul_right _ (Nat.lt_size_self A).le
    _ = 2 ^ (Nat.size A + (n + 2) * D) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (n * lam) := Nat.pow_le_pow_right (by norm_num) key
    _ = (2 ^ n) ^ lam := by rw [← pow_mul]
end MIPRE.Halting

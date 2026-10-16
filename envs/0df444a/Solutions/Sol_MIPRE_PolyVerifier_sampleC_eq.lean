-- Prove2me | solution 1 for MIPRE.PolyVerifier.sampleC_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T19:46:31.347212+00:00
-- url     : https://prove2.me/submissions/fc978c20-5aa3-42e6-a2d3-ec8a43b05e5e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ClassMIPStarTab.lean (solution of MIPRE.PolyVerifier.sampleC_eq);
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
import Definitions.Def_MIPRE_Foundations_ClassMIPStar
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_ClassMIPStarTab
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Machine_runs_of_runForD

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
variable (V : PolyVerifier)
theorem sample?_eq_some_iff (z r : BitStr) (p : BitStr × BitStr) :
    V.sample? z r = some p ↔ ∃ t, V.sampler.Runs (encode (z, r)) (encode p) t := by
  unfold sample?
  split_ifs with h
  · obtain ⟨t, ht⟩ := h.choose_spec
    constructor
    · rintro ⟨rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t', ht'⟩
      obtain ⟨he, -⟩ := ht.deterministic ht'
      have := SizedEncoding.decode_encode (α := BitStr × BitStr) h.choose
      rw [he, SizedEncoding.decode_encode] at this
      rw [Option.some.injEq] at this
      rw [this]
  · simp only [false_iff, not_exists]
    exact fun t ht => h ⟨p, t, ht⟩
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
variable (V : PolyVerifier)
/-- On an efficient verifier the sampler's output on a seed of the right length is the
question pair, with no fallback. -/
theorem questions_eq_of_efficient {z : BitStr} (h : V.Efficient z) {r : BitStr}
    (hr : r.length = V.B z) :
    ∃ (x y : BitStr) (t : ℕ), t ≤ V.bound.eval (z.length + r.length) ∧
      V.sampler.Runs (encode (z, r)) (encode (x, y)) t ∧
      (V.questions z r).1.1 = x ∧ (V.questions z r).2.1 = y := by
  obtain ⟨x, y, t, ht, hx, hy, hrun⟩ := h.sampler_runs r hr
  refine ⟨x, y, t, ht, hrun, ?_⟩
  have hs : V.sample? z r = some (x, y) := (V.sample?_eq_some_iff z r (x, y)).2 ⟨t, hrun⟩
  simp only [questions, hs, hx, hy, and_self, dite_true]
end MIPRE.PolyVerifier

namespace MIPRE.Cost.Machine
/-- **The decision procedure.** For a program that halts within the budget, whether it returns
a given value is decidable. -/
theorem runForD_eq_some_iff {p : Prog} {x r : Data} {k : ℕ}
    (hb : HaltsWithin p x k) : runForD (encode p) x k = some r ↔ ∃ t, p.Runs x r t := by
  obtain ⟨r₀, t₀, ht₀, h₀⟩ := hb
  refine ⟨runs_of_runForD, fun ⟨t, h⟩ => ?_⟩
  obtain ⟨rfl, -⟩ := h₀.deterministic h
  exact runForD_eq_some h₀ ht₀
end MIPRE.Cost.Machine

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
variable (V : PolyVerifier)
theorem _root_.solution {z : BitStr} (h : V.Efficient z) {r : BitStr} (hr : r.length = V.B z) :
    sampleC (encode V.sampler) (V.bound.eval (z.length + V.B z)) z r =
      ((V.questions z r).1.1, (V.questions z r).2.1) := by
  obtain ⟨x, y, t, ht, hrun, hx, hy⟩ := V.questions_eq_of_efficient h hr
  rw [hr] at ht
  have hrf : Machine.runForD (encode V.sampler) (encode (z, r))
      (V.bound.eval (z.length + V.B z)) = some (encode (x, y)) :=
    (Machine.runForD_eq_some_iff ⟨_, t, ht, hrun⟩).2 ⟨t, hrun⟩
  rw [hx, hy]
  simp only [sampleC, hrf, Option.bind_some]
  show ((SizedEncoding.decode (Data.cons (encode x) (encode y)).left : Option BitStr).bind
    fun x' => (SizedEncoding.decode (Data.cons (encode x) (encode y)).right : Option BitStr).map
      fun y' => (x', y')).getD ([], []) = (x, y)
  rw [Data.left_cons, Data.right_cons, SizedEncoding.decode_encode, SizedEncoding.decode_encode]
  rfl
end MIPRE.PolyVerifier

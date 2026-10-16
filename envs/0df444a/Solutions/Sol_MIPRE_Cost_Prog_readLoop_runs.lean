-- Prove2me | solution 1 for MIPRE.Cost.Prog.readLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:09:25.931164+00:00
-- url     : https://prove2.me/submissions/eec076e8-52e3-41b0-847d-04f816f13836

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Compressor.lean (solution of MIPRE.Cost.Prog.readLoop_runs);
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
import Theorems.Thm_MIPRE_Cost_Prog_readBody_bit

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
open Polynomial
open Data
theorem incProg_wellScoped : incProg.WellScoped 1 := by
  simp [incProg, WellScoped, incBody, revOntoProg, revOntoBody]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Cost
open Data
theorem readBody_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (readBody univ).WellScoped 1 := by
  refine ⟨by decide, trivial, by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩, ?_⟩
  refine ⟨callVar_wellScoped (by decide) hU, ?_⟩
  refine ⟨by decide, ⟨callVar_wellScoped (by decide) incProg_wellScoped, by simp [WellScoped]⟩, ?_⟩
  refine ⟨by decide, ⟨callVar_wellScoped (by decide) incProg_wellScoped, by simp [WellScoped]⟩,
    by simp [WellScoped]⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Cost
open Data
variable {univ : Prog} (cD : Data)
theorem readBody_pre (hU : univ.WellScoped 1) {iD acc ans : Data} {t : ℕ}
    (h : univ.Runs (.cons cD iD) ans t) {r : Data} {t' : ℕ}
    (hc : Eval (readEnv cD iD acc ans) readTail r t') :
    Eval [.cons cD (.cons iD acc)] (readBody univ) r
      (t' + t + 2 * cD.size + 2 * iD.size + 10) := by
  have e := Eval.elim_cons (env := [Data.cons cD (.cons iD acc)]) (i := 0) (n := .nil)
    (a := cD) (b := .cons iD acc) (by simp)
    (Eval.elim_cons (i := 1) (n := .nil) (a := iD) (b := acc) (by simp)
      (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := cD) (by simp))
          (Eval.var_of_get (i := 0) (v := iD) (by simp)))
        (Eval.let_ (callVar_eval hU (i := 0) (v := .cons cD iD) (by simp) h) hc)))
  refine e.cast_cost ?_
  simp only [Data.size_cons]
  omega
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Cost
open Data
variable {univ : Prog} (cD : Data)
/-- The body on the marker: stop with the accumulator. -/
theorem readBody_stop (hU : univ.WellScoped 1) {iD acc : Data} {t : ℕ} (h : univ.Runs (.cons cD iD) (Data.ofNat 2) t) :
    Eval [.cons cD (.cons iD acc)] (readBody univ) (.cons .nil acc)
      (t + 2 * cD.size + 2 * iD.size + acc.size + 15) :=
  (readBody_pre cD hU h (Eval.elim_cons (i := 0) (a := .nil) (b := Data.ofNat 1)
      (by simp [readEnv, Data.ofNat])
    (Eval.elim_cons (i := 1) (a := .nil) (b := .nil) (by simp [readEnv, Data.ofNat])
      (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 7) (v := acc) (by simp [readEnv])))))).cast_cost
    (by omega)
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Cost
open Data
theorem _root_.solution (U : UniversalMachine) {c : Prog} {n : ℕ} {x : BitStr}
    (hsd : IsSuccinctDesc c n x) (env : Env) :
    ∃ t ≤ (x.length + 1) * (readIter U (esize c) n x.length + 1),
      Eval (readState (encode c) x 0 :: env) (.loop (readBody U.univ)) (encode x.reverse) t := by
  -- the bit queries, through the universal machine, within the iteration budget
  have hquery : ∀ i, i ≤ x.length → ∃ t ≤ U.bound.eval (esize c + (4 * Nat.size x.length + 1) +
      (n + 1) * (Nat.size x.length + 1) ^ 2),
      U.univ.Runs (.cons (encode c) (encode i)) (bitQueryAnswer x i) t := by
    intro i hi
    obtain ⟨t, ht, hrun⟩ := hsd.2.2 i
    obtain ⟨t', ht', hrun'⟩ := U.time_le c _ _ t hrun
    refine ⟨t', ht'.trans (polynomial_eval_mono U.bound ?_), hrun'⟩
    have h1 : (encode i : Data).size ≤ 4 * Nat.size i + 1 := esize_nat_le i
    have h2 : Nat.size i ≤ Nat.size x.length := Nat.size_le_size hi
    have h3 : (n + 1) * (Nat.size i + 1) ^ 2 ≤ (n + 1) * (Nat.size x.length + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    omega
  have hacc : ∀ i, (encode (x.take i).reverse : Data).size ≤ 4 * x.length + 1 := fun i =>
    (esize_bitStr_le _).trans (by simp only [List.length_reverse, List.length_take]; omega)
  suffices key : ∀ s, (∃ i, i ≤ x.length ∧ s = readState (encode c) x i) →
      ∃ r t, t ≤ (x.length - Data.natOf s.right.left + 1) * (readIter U (esize c) n x.length + 1) ∧
        r = encode x.reverse ∧ Eval (s :: env) (.loop (readBody U.univ)) r t by
    obtain ⟨r, t, ht, rfl, hrun⟩ := key (readState (encode c) x 0) ⟨0, by omega, rfl⟩
    refine ⟨t, ?_, hrun⟩
    simpa [readState, Data.right, Data.left] using ht
  refine Eval.loop_of_invariant (readBody_wellScoped U.closed) env
    (fun s => ∃ i, i ≤ x.length ∧ s = readState (encode c) x i)
    (fun s => x.length - Data.natOf s.right.left)
    (fun r => r = encode x.reverse) (readIter U (esize c) n x.length) ?_
  rintro s ⟨i, hi, rfl⟩
  obtain ⟨t, ht, hrun⟩ := hquery i hi
  have hiD : (encode i : Data).size ≤ 4 * Nat.size x.length + 1 :=
    (esize_nat_le i).trans (by have := Nat.size_le_size hi; omega)
  rcases Nat.lt_or_ge i x.length with hlt | hge
  · -- a bit: continue
    right
    have hans : bitQueryAnswer x i = encode (x.get ⟨i, hlt⟩) := by simp [bitQueryAnswer, hlt]
    rw [hans] at hrun
    obtain ⟨t', ht', hrun'⟩ := readBody_bit (encode c) U.closed (acc := encode (x.take i).reverse)
      rfl (x.get ⟨i, hlt⟩) hrun
    have hst : (encode (x.take (i + 1)).reverse : Data) =
        .cons (encode (x.get ⟨i, hlt⟩)) (encode (x.take i).reverse) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.reverse_append,
        List.reverse_singleton, List.singleton_append, encode_bitStr_cons]
      rfl
    refine ⟨.nil, .nil, readState (encode c) x (i + 1), t', ?_, ?_, ⟨i + 1, hlt, rfl⟩, ?_⟩
    · refine ht'.trans ?_
      unfold readIter
      have h1 : esize i ≤ 4 * Nat.size i + 1 := esize_nat_le i
      have h2 : Nat.size i ≤ Nat.size x.length := Nat.size_le_size hi
      have h3 : (Nat.size i + 2) * (8 * esize i + 8 * Nat.size i + 60) ≤
          (Nat.size x.length + 2) * (8 * (4 * Nat.size x.length + 1) + 8 * Nat.size x.length + 60) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h4 := hacc i
      have h5 : (encode c : Data).size = esize c := rfl
      omega
    · unfold readState; rw [hst]; exact hrun'
    · simp only [readState, Data.right, Data.left, Data.natOf_encode]
      omega
  · -- the marker: stop
    left
    have hans : bitQueryAnswer x i = Data.ofNat 2 := by simp [bitQueryAnswer, not_lt.2 hge]
    rw [hans] at hrun
    refine ⟨_, _, ?_, readBody_stop (encode c) U.closed hrun, ?_⟩
    · unfold readIter
      have h4 := hacc i
      have h5 : (encode c : Data).size = esize c := rfl
      have h6 : 0 ≤ (Nat.size x.length + 2) *
        (8 * (4 * Nat.size x.length + 1) + 8 * Nat.size x.length + 60) := Nat.zero_le _
      omega
    · have : i = x.length := le_antisymm hi hge
      subst this
      simp
end MIPRE.Cost.Prog

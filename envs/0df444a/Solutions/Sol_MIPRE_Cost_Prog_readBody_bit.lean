-- Prove2me | solution 1 for MIPRE.Cost.Prog.readBody_bit
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:06:57.794479+00:00
-- url     : https://prove2.me/submissions/c7d58337-c142-4c66-949b-9e6d68648772

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Compressor.lean (solution of MIPRE.Cost.Prog.readBody_bit);
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
import Theorems.Thm_MIPRE_Cost_Prog_incProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Data
open Polynomial
theorem bitsVal_inc (l : BitStr) : bitsVal (inc l) = bitsVal l + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b
    · simp [inc, bitsVal_cons, Nat.bit]
    · simp only [inc, bitsVal_cons, ih, Nat.bit]
      simp only [Bool.cond_false, Bool.cond_true]
      omega
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
open Polynomial
theorem inc_ne_nil (l : BitStr) : inc l ≠ [] := by
  cases l with
  | nil => simp [inc]
  | cons b l => cases b <;> simp [inc]
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
open Polynomial
theorem inc_canon (l : BitStr) (hl : l = [] ∨ l.getLast? = some true) :
    (inc l).getLast? = some true := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hl' : l = [] ∨ l.getLast? = some true := by
      rcases hl with h | h
      · cases h
      · rcases l with _ | ⟨c, l⟩
        · exact Or.inl rfl
        · right; rw [List.getLast?_cons_cons] at h; exact h
    cases b
    · simp only [inc]
      rcases l with _ | ⟨c, l⟩
      · rfl
      · rw [List.getLast?_cons_cons]
        rcases hl' with h | h
        · cases h
        · exact h
    · simp only [inc]
      rcases hinc : inc l with _ | ⟨c, l'⟩
      · exact absurd hinc (inc_ne_nil l)
      · rw [List.getLast?_cons_cons, ← hinc]
        exact ih hl'
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
open Polynomial
/-- The successor on canonical binary numerals is the successor. -/
theorem inc_bits (n : ℕ) : inc n.bits = (n + 1).bits := by
  have hcanon : inc n.bits = [] ∨ (inc n.bits).getLast? = some true :=
    Or.inr (inc_canon n.bits (bits_getLast n))
  have := bits_foldr_of_canon (inc n.bits) hcanon
  rw [← this]
  congr 1
  show bitsVal (inc n.bits) = n + 1
  rw [bitsVal_inc, bitsVal_bits]
end MIPRE.Cost.Data

namespace MIPRE.Cost.Prog
open Polynomial
open Data
theorem incProg_wellScoped : incProg.WellScoped 1 := by
  simp [incProg, WellScoped, incBody, revOntoProg, revOntoBody]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Polynomial
open Data
/-- The successor on canonical numerals, as a run on `encode n`. -/
theorem incProg_runs_nat (n : ℕ) :
    ∃ t ≤ (Nat.size n + 2) * (8 * esize n + 8 * Nat.size n + 60),
      incProg.Runs (encode n) (encode (n + 1)) t := by
  obtain ⟨t, ht, h⟩ := incProg_runs n.bits
  refine ⟨t, ?_, ?_⟩
  · rw [← Nat.size_eq_bits_len]; exact ht
  · show incProg.Runs (encode n.bits) (encode (n + 1).bits) t
    rw [← inc_bits]; exact h
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Cost
open Data
variable {univ : Prog} (cD : Data)
theorem _root_.solution (hU : univ.WellScoped 1) {iD acc : Data} {i : ℕ} (hi : iD = encode i) (b : Bool) {t : ℕ}
    (h : univ.Runs (.cons cD iD) (encode b) t) :
    ∃ t' ≤ t + 3 * cD.size + 4 * iD.size + acc.size +
        2 * ((Nat.size i + 2) * (8 * esize i + 8 * Nat.size i + 60)) + 30,
      Eval [.cons cD (.cons iD acc)] (readBody univ)
        (.cons (.cons .nil .nil) (.cons cD (.cons (encode (i + 1)) (.cons (encode b) acc)))) t' := by
  obtain ⟨ti, hti, hinc⟩ := incProg_runs_nat i
  subst hi
  cases b with
  | false =>
    refine ⟨_, ?_, readBody_pre cD hU h (Eval.elim_nil (i := 0) (by simp [readEnv])
      (Eval.let_ (callVar_eval incProg_wellScoped (i := 2) (v := encode i) (by simp [readEnv]) hinc)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.cons (Eval.var_of_get (i := 5) (v := cD) (by simp [readEnv]))
            (Eval.cons (Eval.var_of_get (i := 0) (v := encode (i + 1)) (by simp))
              (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 4) (v := acc) (by simp [readEnv]))))))))⟩
    have hei : esize i = (encode i : Data).size := rfl
    have : (encode (i + 1) : Data).size ≤ ti := hinc.size_le
    omega
  | true =>
    refine ⟨_, ?_, readBody_pre cD hU h (Eval.elim_cons (i := 0) (a := .nil) (b := .nil)
        (by simp [readEnv])
      (Eval.elim_nil (i := 1) (by simp [readEnv])
        (Eval.let_ (callVar_eval incProg_wellScoped (i := 4) (v := encode i) (by simp [readEnv]) hinc)
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 7) (v := cD) (by simp [readEnv]))
              (Eval.cons (Eval.var_of_get (i := 0) (v := encode (i + 1)) (by simp))
                (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                  (Eval.var_of_get (i := 6) (v := acc) (by simp [readEnv])))))))))⟩
    have hei : esize i = (encode i : Data).size := rfl
    have : (encode (i + 1) : Data).size ≤ ti := hinc.size_le
    omega
end MIPRE.Cost.Prog

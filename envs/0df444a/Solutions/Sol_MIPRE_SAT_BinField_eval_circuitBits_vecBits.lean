-- Prove2me | solution 1 for MIPRE.SAT.BinField.eval_circuitBits_vecBits
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:48:49.971516+00:00
-- url     : https://prove2.me/submissions/a2365404-e57d-4d70-b582-4d75e0029cc5

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/FieldVectors.lean (solution of MIPRE.SAT.BinField.eval_circuitBits_vecBits);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_GateProg
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_InputRoutingProg
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_SAT_GateFieldEval
import Definitions.Def_MIPRE_Foundations_SAT_CircuitFieldEval
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization
import Definitions.Def_MIPRE_Foundations_SAT_CircuitFieldCorrect
import Definitions.Def_MIPRE_Foundations_SAT_FieldVectors
import Theorems.Thm_MIPRE_SAT_Circuit_evalBits_circuitBits_finite

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
attribute [instance] MIPRE.SAT.BinField.instField MIPRE.SAT.BinField.instFintype MIPRE.SAT.BinField.instDecidableEq

namespace MIPRE.SAT.BinField
noncomputable section
open Cost LowDegree MvPolynomial
variable {k : ℕ} (E : BinField k)
attribute [instance] MIPRE.SAT.BinField.instField MIPRE.SAT.BinField.instFintype MIPRE.SAT.BinField.instDecidableEq
theorem width_vecBits {n : ℕ} (v : Fin n → E.carrier) {b : Cost.BitStr} (hb : b ∈ E.vecBits v) :
    b.length = k := by
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hb
  exact E.length_toBits a
end
end MIPRE.SAT.BinField

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.BinField
open Cost LowDegree LowDegree.BinaryPolynomial
variable {k : ℕ} (E : BinField k)
theorem _root_.solution (C : Circuit) (hC : C.WellFormed)
    (p : BitStr) (hp : p ≠ []) (hpk : p.length = k)
    [CharP E.carrier 2] (root : E.carrier)
    (hroot : root ^ p.length = BinaryPolynomial.evalBits root p)
    (hencode : ∀ a : E.carrier, BinaryPolynomial.evalBits root (E.toBits a) = a)
    (v : Fin (C.inputs + C.size) → E.carrier) :
    BinaryPolynomial.evalBits root (Circuit.circuitBits p
      ((E.vecBits v).take C.inputs) ((E.vecBits v).drop C.inputs) C.gates) =
      MvPolynomial.eval v C.finiteArith := by
  let x := (E.vecBits v).take C.inputs
  let w := (E.vecBits v).drop C.inputs
  have hxlen : x.length = C.inputs := by simp [x]
  have hwlen : w.length = C.size := by simp [w]
  have hx : ∀ b ∈ x, b.length = p.length := by
    intro b hb
    exact (E.width_vecBits v (List.mem_of_mem_take hb)).trans hpk.symm
  have hw : ∀ b ∈ w, b.length = p.length := by
    intro b hb
    exact (E.width_vecBits v (List.mem_of_mem_drop hb)).trans hpk.symm
  rw [Circuit.evalBits_circuitBits_finite C hC root p hp hroot x w hxlen hwlen hx hw]
  congr 2
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [Fin.addCases_left]
    have hg : x.getD a [] = E.toBits (v (Fin.castAdd C.size a)) := by
      simp only [x, List.getD_eq_getElem?_getD]
      rw [List.getElem?_take_of_lt a.isLt]
      exact getD_vecBits E v (Fin.castAdd C.size a)
    rw [hg, hencode]
  · simp only [Fin.addCases_right]
    have hg : w.getD b [] = E.toBits (v (Fin.natAdd C.inputs b)) := by
      simp only [w, List.getD_eq_getElem?_getD, List.getElem?_drop]
      exact getD_vecBits E v (Fin.natAdd C.inputs b)
    rw [hg, hencode]
end MIPRE.SAT.BinField

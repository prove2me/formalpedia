-- Prove2me | solution 1 for MIPRE.SAT.PcpParams.exists_point_of_clause_mem
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:27:38.369421+00:00
-- url     : https://prove2.me/submissions/c79233d2-77b7-4cc3-8787-3d8dbffe3208

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/PcpCircuit.lean (solution of MIPRE.SAT.PcpParams.exists_point_of_clause_mem);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Computability.Language
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
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
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra
import Definitions.Def_MIPRE_Foundations_SAT_PcpBlocks
import Definitions.Def_MIPRE_TM_CookLevin_PcpClauses
import Definitions.Def_MIPRE_TM_CookLevin_PcpCircuit
import Theorems.Thm_MIPRE_SAT_Circuit_eval_iff_exists_finiteArith

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.PcpParams
noncomputable section
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
theorem eval_circuitArith (P : PcpParams) (C : Circuit) (h : C.inputs + C.size = P.m')
    (y : Fin P.m' → F) :
    eval y (P.circuitArith C h) = eval (y ∘ Fin.cast h) C.finiteArith := by
  simp only [circuitArith, MvPolynomial.eval_rename]
end
end MIPRE.SAT.PcpParams

namespace MIPRE.SAT.PcpParams
noncomputable section
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
/-- Every accepting input extends to a Boolean PCP point on which the circuit
polynomial is one, and all its original input coordinates are retained. -/
theorem eval_iff_exists_circuitArith (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (h : C.inputs + C.size = P.m') (x : ℕ → Bool) :
    C.eval x = true ↔ ∃ y : Fin P.m' → Bool,
      (∀ i : Fin C.inputs, y (Fin.cast h (Fin.castAdd C.size i)) = x i) ∧
      eval (pt y) (P.circuitArith (F := F) C h) = 1 := by
  rw [C.eval_iff_exists_finiteArith (F := F) hC]
  constructor
  · rintro ⟨u, hu, he⟩
    refine ⟨u ∘ Fin.cast h.symm, ?_, ?_⟩
    · simpa using hu
    · simpa [eval_circuitArith, Function.comp_def, pt] using he
  · rintro ⟨y, hy, he⟩
    refine ⟨y ∘ Fin.cast h, hy, ?_⟩
    simpa [eval_circuitArith, Function.comp_def, pt] using he
end
end MIPRE.SAT.PcpParams

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.PcpParams
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
theorem _root_.solution (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
    (c : Clause5 (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) (Fin (2 ^ P.m))
      (Fin (2 ^ P.m)) (Fin (2 ^ P.m))) (hc : c ∈ C.formula5 P.m P.m) :
    ∃ y : Fin P.m' → Bool, P.pointClause y = c ∧
      eval (pt y) (P.circuitArith (F := F) C h) = 1 := by
  obtain ⟨y, hy, he⟩ := (P.eval_iff_exists_circuitArith (F := F) C hC h
    (fun j => (clauseInput5 P.m P.m c).getD j false)).mp hc
  refine ⟨y, ?_, he⟩
  apply clauseInput5_injective P.m
  rw [clauseInput5_pointClause]
  apply List.ext_getElem
  · simp only [length_inputSlice, length_clauseInput5]
    omega
  · intro j hj hj'
    have hji : j < C.inputs := by rw [hI]; simpa using hj
    have hh := hy ⟨j, hji⟩
    change y ⟨j, _⟩ = _ at hh
    simpa only [inputSlice, List.getElem_ofFn,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some] using hh
end MIPRE.SAT.PcpParams

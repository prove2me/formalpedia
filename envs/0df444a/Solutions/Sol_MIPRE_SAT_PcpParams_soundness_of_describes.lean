-- Prove2me | solution 1 for MIPRE.SAT.PcpParams.soundness_of_describes
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:32:56.657562+00:00
-- url     : https://prove2.me/submissions/bde20fc1-dc9d-46e6-b689-b635479dd969

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/PcpCircuit.lean (solution of MIPRE.SAT.PcpParams.soundness_of_describes);
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
import Theorems.Thm_MIPRE_SAT_PcpParams_formula5_sat_of_majority

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [CommRing F] {m : ℕ}
variable [DecidableEq F]
/-- `Coded g` is always `{0,1}`-valued. -/
theorem coded_eq (g : MvPolynomial (Fin m) F) (y : Fin m → Bool) :
    coded g y = 0 ∨ coded g y = 1 := by
  by_cases h : eval (pt y) g ∈ ({0, 1} : Finset F)
  · have hv : eval (pt y) g = 0 ∨ eval (pt y) g = 1 := by simpa using h
    simpa only [coded, codedOn, if_pos h] using hv
  · exact Or.inl (by simp [coded, codedOn, h])
end
end MIPRE.LowDegree

namespace MIPRE.SAT.PcpParams
noncomputable section
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
theorem ofBool_decodedAssignment [DecidableEq F] {P : PcpParams} (pf : PcpProof P F)
    (i : Fin 5) (j : Fin (2 ^ P.m)) :
    (ofBool (decodedAssignment pf i j) : F) = coded (pf.g i) (indexCube j) := by
  rcases coded_eq (pf.g i) (indexCube j) with h | h <;>
    simp [decodedAssignment, h, ofBool]
end
end MIPRE.SAT.PcpParams

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.PcpParams
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
theorem _root_.solution [Fintype F] [DecidableEq F]
    (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
    (D : Decider) (n T : ℕ) (x y : Cost.BitStr)
    (hD : C.DescribesDecider P.m P.m D n x y T)
    (pf : PcpProof P F) (hq : 82 * P.m' ≤ Fintype.card F)
    (S : Finset (Fin P.m' → F))
    (hS : ∀ z ∈ S, PcpAlgebra.TypedAccepts (P.circuitArith C h) z (pf.ev z))
    (hmajority : Fintype.card F ^ P.m' < 2 * S.card) :
    ∃ ap bp : Cost.BitStr, ap.length ≤ T ∧ bp.length ≤ T ∧
      D.AcceptsWithin n x y ap bp T ∧
      coded (pf.g 0) = answerVec F P.m ap ∧ coded (pf.g 1) = answerVec F P.m bp := by
  have hs := P.formula5_sat_of_majority C hC hI h pf hq S hS hmajority
  obtain ⟨ap, bp, hap, hbp, ha, hb, hacc⟩ :=
    (hD (decodedAssignment pf 0) (decodedAssignment pf 1)).mp ⟨_, _, _, hs⟩
  refine ⟨ap, bp, hap, hbp, hacc, ?_, ?_⟩
  · funext u
    have he := ofBool_decodedAssignment pf 0 (cubeIndex u)
    rw [indexCube_cubeIndex, ha] at he
    exact he.symm
  · funext u
    have he := ofBool_decodedAssignment pf 1 (cubeIndex u)
    rw [indexCube_cubeIndex, hb] at he
    exact he.symm
end MIPRE.SAT.PcpParams

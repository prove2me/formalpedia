-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Pad.verifierCircuitValue_typed
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:40:30.934221+00:00
-- url     : https://prove2.me/submissions/ee519e94-1853-4f9d-b5ed-7a62a3a07126

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/PcpBridge.lean (solution of MIPRE.TM.CookLevin.Pad.verifierCircuitValue_typed);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
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
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
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
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerDispatch
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleConstructor
import Definitions.Def_MIPRE_Foundations_LowDegree_Shoup
import Definitions.Def_MIPRE_Foundations_LowDegree_ShoupCoefficients
import Definitions.Def_MIPRE_Foundations_SAT_QuotientField
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_SAT_PcpFormat
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Definitions.Def_MIPRE_TM_CookLevin_Window
import Definitions.Def_MIPRE_TM_CookLevin_FamilyFml
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run
import Definitions.Def_MIPRE_Foundations_SAT_Table
import Definitions.Def_MIPRE_TM_CookLevin_Params
import Definitions.Def_MIPRE_TM_CookLevin_AnsEnd
import Definitions.Def_MIPRE_TM_CookLevin_Index
import Definitions.Def_MIPRE_TM_CookLevin_Describer
import Definitions.Def_MIPRE_TM_CookLevin_LayoutProg
import Definitions.Def_MIPRE_TM_CookLevin_FieldProg
import Definitions.Def_MIPRE_TM_CookLevin_FamilyProg
import Definitions.Def_MIPRE_TM_CookLevin_DescProg
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Definitions.Def_MIPRE_TM_CookLevin_Sat
import Definitions.Def_MIPRE_TM_CookLevin_Assemble
import Definitions.Def_MIPRE_TM_CookLevin_Link
import Definitions.Def_MIPRE_TM_CookLevin_Decoupled
import Definitions.Def_MIPRE_TM_CookLevin_DecoupledProg
import Definitions.Def_MIPRE_Foundations_SAT_Padding
import Definitions.Def_MIPRE_Foundations_SAT_Rename
import Definitions.Def_MIPRE_Foundations_SAT_PowerPadding
import Definitions.Def_MIPRE_TM_CookLevin_Padded
import Definitions.Def_MIPRE_Foundations_SAT_GatePadding
import Definitions.Def_MIPRE_TM_CookLevin_ExactPadding
import Definitions.Def_MIPRE_TM_CookLevin_PaddingParams
import Definitions.Def_MIPRE_TM_CookLevin_PcpParameters
import Definitions.Def_MIPRE_TM_CookLevin_PcpPrepare
import Definitions.Def_MIPRE_Foundations_SAT_GateProg
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_InputRoutingProg
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_SAT_GateFieldEval
import Definitions.Def_MIPRE_Foundations_SAT_PcpFieldTests
import Definitions.Def_MIPRE_Foundations_SAT_CircuitFieldEval
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization
import Definitions.Def_MIPRE_Foundations_SAT_CircuitFieldCorrect
import Definitions.Def_MIPRE_TM_CookLevin_PcpVerifier
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra
import Definitions.Def_MIPRE_Foundations_SAT_PcpBlocks
import Definitions.Def_MIPRE_TM_CookLevin_PcpClauses
import Definitions.Def_MIPRE_TM_CookLevin_PcpCircuit
import Definitions.Def_MIPRE_Foundations_SAT_FieldVectors
import Definitions.Def_MIPRE_Foundations_SAT_PcpViewTests
import Definitions.Def_MIPRE_TM_CookLevin_PcpBridge
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_monic
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_natDegree
import Theorems.Thm_MIPRE_SAT_BinField_eval_circuitBits_vecBits
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_fixedCircuit_inputs
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_fixedCircuit_wellFormed
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_outerDimProg_apply
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_pcpParams_degree_pos

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

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
/-- The polynomial used by Shoup's contract reads the same coefficient bits. -/
theorem coeff_polyOfBits (l : BitStr) (i : ℕ) :
    (polyOfBits l).coeff i = ofBool (l.getD i false) := by
  simp only [polyOfBits, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hi : i < l.length
  · simp [hi, ofBool]
  · simp [hi, ofBool, List.getD_eq_getElem?_getD]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
/-- A monic polynomial's leading coefficient is present in its coefficient list. -/
theorem natDegree_lt_length (l : BitStr) (h : (polyOfBits l).Monic) :
    (polyOfBits l).natDegree < l.length := by
  have hc : (polyOfBits l).coeff (polyOfBits l).natDegree = 1 := h.coeff_natDegree
  by_contra hn
  rw [coeff_polyOfBits] at hc
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega :
    l.length ≤ (polyOfBits l).natDegree), ofBool] at hc
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
theorem shoupLowerCoeffs_length (k : ℕ) (hk : 1 ≤ k) :
    (shoupLowerCoeffs (unary k)).length = k := by
  have h := natDegree_lt_length (shoupIrreducible (unary k)) (shoupIrreducible_monic k hk)
  rw [shoupIrreducible_natDegree k hk] at h
  simp [shoupLowerCoeffs, min_eq_left (by omega : k ≤ (shoupIrreducible (unary k)).length)]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
theorem innerDimParamsU_length (p : ParamInput) :
    (innerDimParamsU p).length = innerDim p.2.1 p.2.2.2 := by
  simp [innerDimParamsU, innerDim, mParam]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
theorem fieldDegreeU_length (p : ParamInput) :
    (fieldDegreeU p).length = (pcpParams p.1 p.2.1 p.2.2.1 p.2.2.2).k := by
  simp [fieldDegreeU, pcpParams, fieldDegree, outerDimProg_apply, sq]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
set_option maxRecDepth 4096
theorem inputCountU_length (p : ParamInput) :
    (inputCountU p).length = 5 * innerDim p.2.1 p.2.2.2 + 5 := by
  simp [inputCountU, innerDimParamsU_length]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
set_option maxRecDepth 4096
theorem gateBudgetProg_length (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    (gateBudgetProg (pcpInput D n T Q σ x y z ev)).length =
      z.length - (5 * innerDim T σ + 5) := by
  simp [gateBudgetProg, pcpInput, inputCountU_length]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
set_option maxRecDepth 4096
theorem gateBudgetProg_exact (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr)
    (hf : ViewFormat (pcpParams n T Q σ) z ev) :
    (gateBudgetProg (pcpInput D n T Q σ x y z ev)).length = gateCount n T Q σ := by
  rw [gateBudgetProg_length, hf.length_z]
  change 5 * innerDim T σ + 5 + gateCount n T Q σ - (5 * innerDim T σ + 5) = _
  omega
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
set_option maxRecDepth 4096
theorem pcpCircuitProg_apply (p : PcpInput) :
    pcpCircuitProg p = describeExact (p.1, gateBudgetProg p) := rfl
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
set_option maxRecDepth 4096
/-- For a correctly formatted view, the constructor is independent of the
coordinate values and equals the fixed exact-size describer for the specification. -/
theorem pcpCircuitProg_eq_fixed (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr)
    (hf : ViewFormat (pcpParams n T Q σ) z ev) :
    pcpCircuitProg (pcpInput D n T Q σ x y z ev) =
      describeExact (((D, n, T, Q, σ), x, y), unary (gateCount n T Q σ)) := by
  rw [pcpCircuitProg_apply]
  have hb : gateBudgetProg (pcpInput D n T Q σ x y z ev) = unary (gateCount n T Q σ) := by
    apply List.ext_getElem
    · rw [gateBudgetProg_exact D n T Q σ x y z ev hf, length_unary]
    · intro i hi hj
      exact Subsingleton.elim _ _
  rw [hb]
  rfl
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
set_option maxRecDepth 4096
theorem fieldDegreeU_apply (p : ParamInput) :
    fieldDegreeU p = unary ((pcpParams p.1 p.2.1 p.2.2.1 p.2.2.2).k) := by
  apply List.ext_getElem
  · rw [fieldDegreeU_length, length_unary]
  · intro i hi hj
    exact Subsingleton.elim _ _
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc LowDegree LowDegree.BinaryPolynomial
set_option maxRecDepth 4096
theorem verifierModulus_apply (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    verifierModulus (pcpInput D n T Q σ x y z ev) =
      shoupLowerCoeffs (unary (pcpParams n T Q σ).k) := by
  simp only [verifierModulus, comp_apply, fieldDegreeU_apply, verifierParams,
    fst_apply, snd_apply, pcpInput]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc LowDegree LowDegree.BinaryPolynomial
set_option maxRecDepth 4096
theorem verifierCircuitValue_apply (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    verifierCircuitValue (pcpInput D n T Q σ x y z ev) =
      Circuit.circuitBits (verifierModulus (pcpInput D n T Q σ x y z ev))
        (z.take (5 * (pcpParams n T Q σ).m + 5))
        (z.drop (5 * (pcpParams n T Q σ).m + 5))
        (pcpCircuitProg (pcpInput D n T Q σ x y z ev)).gates := by
  simp only [verifierCircuitValue, comp_apply, pair_apply, Circuit.circuitBitsProg_apply,
    take_apply, drop_apply, pointProg, fst_apply, snd_apply, inputCountU_length,
    verifierParams, Circuit.partsProg, ofEncodeEq_apply, pcpInput, pcpParams]
end
end MIPRE.TM.CookLevin.Pad

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

namespace MIPRE.SAT.BinField
section
open Cost LowDegree LowDegree.BinaryPolynomial
variable {k : ℕ} (E : BinField k)
theorem vecBits_cast {n m : ℕ} (h : n = m) (v : Fin m → E.carrier) :
    E.vecBits (v ∘ Fin.cast h) = E.vecBits v := by
  subst m
  rfl
end
end MIPRE.SAT.BinField

namespace MIPRE.TM.CookLevin.Pad
noncomputable section
open SAT Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial
set_option maxRecDepth 4096
theorem pcpModulus_length (n T Q σ : ℕ) : (pcpModulus n T Q σ).length = (pcpParams n T Q σ).k :=
  shoupLowerCoeffs_length _ (pcpParams_degree_pos n T Q σ)
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
noncomputable section
open SAT Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial
set_option maxRecDepth 4096
theorem pcpModulus_ne_nil (n T Q σ : ℕ) : pcpModulus n T Q σ ≠ [] := by
  intro h
  have hl := pcpModulus_length n T Q σ
  have hp := pcpParams_degree_pos n T Q σ
  rw [h, List.length_nil] at hl
  omega
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
noncomputable section
open SAT Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial
set_option maxRecDepth 4096
theorem viewFormat_typed (P : PcpParams) (E : BinField P.k) (z : Fin P.m' → E.carrier)
    (α : Fin 5 → E.carrier) (β : Fin (P.m' + 1) → E.carrier) :
    ViewFormat P (E.vecBits z) (E.vecBits α ++ E.vecBits β) where
  length_z := E.length_vecBits z
  length_ev := by simp; omega
  width_z b hb := E.width_vecBits z hb
  width_ev b hb := by
    rcases List.mem_append.mp hb with h | h
    · exact E.width_vecBits α h
    · exact E.width_vecBits β h
end
end MIPRE.TM.CookLevin.Pad

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Pad
open SAT Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial
set_option maxRecDepth 4096
theorem _root_.solution (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) (E : BinField (pcpParams n T Q σ).k) [CharP E.carrier 2]
    (root : E.carrier)
    (hroot : root ^ (pcpModulus n T Q σ).length = BinaryPolynomial.evalBits root (pcpModulus n T Q σ))
    (hencode : ∀ a : E.carrier, BinaryPolynomial.evalBits root (E.toBits a) = a)
    (z : Fin (pcpParams n T Q σ).m' → E.carrier)
    (α : Fin 5 → E.carrier) (β : Fin ((pcpParams n T Q σ).m' + 1) → E.carrier) :
    BinaryPolynomial.evalBits root (verifierCircuitValue
      (pcpInput D n T Q σ x y (E.vecBits z) (E.vecBits α ++ E.vecBits β))) =
      eval z (clausePolynomial D n T Q σ x y hV) := by
  let C := fixedCircuit D n T Q σ x y
  have hC := fixedCircuit_wellFormed D n T Q σ x y
  have hI := fixedCircuit_inputs D n T Q σ x y
  have hvars := fixedCircuit_variables D n T Q σ x y hV
  have hf := viewFormat_typed (pcpParams n T Q σ) E z α β
  have he := E.eval_circuitBits_vecBits C hC (pcpModulus n T Q σ) (pcpModulus_ne_nil n T Q σ)
    (pcpModulus_length n T Q σ) root hroot hencode (z ∘ Fin.cast hvars)
  rw [E.vecBits_cast] at he
  rw [verifierCircuitValue_apply, verifierModulus_apply, pcpCircuitProg_eq_fixed D n T Q σ x y _ _ hf]
  change BinaryPolynomial.evalBits root (Circuit.circuitBits (pcpModulus n T Q σ)
    ((E.vecBits z).take (5 * (pcpParams n T Q σ).m + 5))
    ((E.vecBits z).drop (5 * (pcpParams n T Q σ).m + 5)) C.gates) = _
  rw [← hI]
  exact he.trans ((pcpParams n T Q σ).eval_circuitArith C hvars z).symm
end MIPRE.TM.CookLevin.Pad

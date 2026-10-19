-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Pad.verifierTests_typed_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:46:08.310238+00:00
-- url     : https://prove2.me/submissions/229523a4-1a58-4302-aa0c-8263c3c5ae50

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/PcpBridge.lean (solution of MIPRE.TM.CookLevin.Pad.verifierTests_typed_iff);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_monic
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_natDegree
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_outerDimProg_apply
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_pcpParams_degree_pos
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_verifierCircuitValue_typed

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

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
theorem arithmeticFold_cons (mul : Bool) (p a b : BitStr) (l : List BitStr) :
    arithmeticFold mul p a (b :: l) =
      arithmeticFold mul p (if mul then mulReduce p a b else xorBits a b) l := rfl
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
theorem arithmeticFold_add_width (p a : BitStr) (l : List BitStr) (ha : a.length = p.length)
    (hl : ∀ b ∈ l, b.length = p.length) :
    (arithmeticFold false p a l).length = p.length := by
  induction l generalizing a with
  | nil => exact ha
  | cons b l ih =>
    apply ih _ (by simp only [Bool.false_eq_true, if_false, length_xorBits, ha, hl b (by simp), min_self])
    exact fun c hc => hl c (by simp [hc])
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
/-- A modular product fold computes the product of all decoded operands. -/
theorem evalBits_arithmeticFold_mul (z : R) (p a : BitStr) (l : List BitStr)
    (ha : a.length = p.length) (hroot : z ^ p.length = evalBits z p) :
    evalBits z (arithmeticFold true p a l) = evalBits z a * (l.map (evalBits z)).prod := by
  induction l generalizing a with
  | nil => simp [arithmeticFold]
  | cons b l ih =>
    rw [arithmeticFold_cons]
    simp only [if_true]
    rw [ih _ (length_mulReduce _ _ _ ha), evalBits_mulReduce z p _ _ ha hroot]
    simp only [List.map_cons, List.prod_cons, mul_assoc]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
/-- A fixed-width XOR fold computes the sum of all decoded operands. -/
theorem evalBits_arithmeticFold_add (z : R) (p a : BitStr) (l : List BitStr)
    (ha : a.length = p.length) (hl : ∀ b ∈ l, b.length = p.length) :
    evalBits z (arithmeticFold false p a l) = evalBits z a + (l.map (evalBits z)).sum := by
  induction l generalizing a with
  | nil => simp [arithmeticFold]
  | cons b l ih =>
    have hb := hl b (by simp)
    rw [arithmeticFold_cons]
    simp only [Bool.false_eq_true, if_false]
    rw [ih _ (by simp only [length_xorBits, ha, hb, min_self])
      (fun c hc => hl c (by simp [hc])), evalBits_xor z a b (ha.trans hb.symm)]
    simp only [List.map_cons, List.sum_cons, add_assoc]
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

namespace MIPRE.SAT.PcpFieldTests
section
open Cost LowDegree LowDegree.BinaryPolynomial
theorem length_formulaValue (p φ : BitStr) (l : List (BitStr × BitStr))
    (hφ : φ.length = p.length) : (formulaValue p φ l).length = p.length :=
  length_mulReduce _ _ _ hφ
end
end MIPRE.SAT.PcpFieldTests

namespace MIPRE.SAT.PcpFieldTests
section
open Cost LowDegree LowDegree.BinaryPolynomial
theorem length_certificateTerm (p : BitStr) (a : BitStr × BitStr) (ha : a.1.length = p.length) :
    (certificateTerm p a).length = p.length := length_mulReduce _ _ _ ha
end
end MIPRE.SAT.PcpFieldTests

namespace MIPRE.SAT.PcpFieldTests
section
open Cost LowDegree LowDegree.BinaryPolynomial
theorem length_certificateValue (p : BitStr) (l : List (BitStr × BitStr)) (hl : CorrectPairs p l) :
    (certificateValue p l).length = p.length := by
  apply arithmeticFold_add_width _ _ _ (length_zeroBits p)
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  exact length_certificateTerm p a (hl a ha).1
end
end MIPRE.SAT.PcpFieldTests

namespace MIPRE.SAT.PcpFieldTests
section
open Cost LowDegree LowDegree.BinaryPolynomial
variable {R : Type*} [CommRing R] [CharP R 2]
theorem eval_literalProduct (z : R) (p : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (l : List (BitStr × BitStr)) (hl : CorrectPairs p l) :
    BinaryPolynomial.evalBits z (literalProduct p l) =
      (l.map (fun a => BinaryPolynomial.evalBits z a.1 - BinaryPolynomial.evalBits z a.2)).prod := by
  rw [literalProduct, evalBits_arithmeticFold_mul z p _ _ (length_oneBits p) hroot,
    evalBits_oneBits z p hp, one_mul, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a ha
  simp only [Function.comp_apply]
  rw [evalBits_xor z _ _ ((hl a ha).1.trans (hl a ha).2.symm), CharTwo.sub_eq_add]
end
end MIPRE.SAT.PcpFieldTests

namespace MIPRE.SAT.PcpFieldTests
section
open Cost LowDegree LowDegree.BinaryPolynomial
variable {R : Type*} [CommRing R] [CharP R 2]
theorem eval_formulaValue (z : R) (p : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (φ : BitStr) (hφ : φ.length = p.length)
    (l : List (BitStr × BitStr)) (hl : CorrectPairs p l) :
    BinaryPolynomial.evalBits z (formulaValue p φ l) = BinaryPolynomial.evalBits z φ *
      (l.map (fun a => BinaryPolynomial.evalBits z a.1 - BinaryPolynomial.evalBits z a.2)).prod := by
  rw [formulaValue, evalBits_mulReduce z p _ _ hφ hroot, eval_literalProduct z p hp hroot l hl]
end
end MIPRE.SAT.PcpFieldTests

namespace MIPRE.SAT.PcpFieldTests
section
open Cost LowDegree LowDegree.BinaryPolynomial
variable {R : Type*} [CommRing R] [CharP R 2]
theorem eval_certificateTerm (z : R) (p : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (a : BitStr × BitStr) (ha : a.1.length = p.length) (hb : a.2.length = p.length) :
    BinaryPolynomial.evalBits z (certificateTerm p a) = BinaryPolynomial.evalBits z a.1 *
      (BinaryPolynomial.evalBits z a.2 * (1 - BinaryPolynomial.evalBits z a.2)) := by
  rw [certificateTerm, evalBits_mulReduce z p _ _ ha hroot,
    evalBits_mulReduce z p _ _ hb hroot,
    evalBits_xor z _ _ ((length_oneBits p).trans hb.symm), evalBits_oneBits z p hp,
    CharTwo.sub_eq_add]
end
end MIPRE.SAT.PcpFieldTests

namespace MIPRE.SAT.PcpFieldTests
section
open Cost LowDegree LowDegree.BinaryPolynomial
variable {R : Type*} [CommRing R] [CharP R 2]
theorem eval_certificateValue (z : R) (p : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (l : List (BitStr × BitStr)) (hl : CorrectPairs p l) :
    BinaryPolynomial.evalBits z (certificateValue p l) =
      (l.map (fun a => BinaryPolynomial.evalBits z a.1 *
        (BinaryPolynomial.evalBits z a.2 * (1 - BinaryPolynomial.evalBits z a.2)))).sum := by
  have hw : ∀ b ∈ l.map (certificateTerm p), b.length = p.length := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact length_certificateTerm p a (hl a ha).1
  rw [certificateValue, evalBits_arithmeticFold_add z p _ _ (length_zeroBits p) hw,
    evalBits_zeroBits, zero_add, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact eval_certificateTerm z p hp hroot a (hl a ha).1 (hl a ha).2
end
end MIPRE.SAT.PcpFieldTests

namespace MIPRE.SAT.PcpFieldTests
section
open Cost LowDegree LowDegree.BinaryPolynomial
variable {R : Type*} [CommRing R] [CharP R 2]
/-- Faithful coefficient decoding converts the two executable equality checks
into precisely the two algebraic field identities. -/
theorem checksProg_true_iff (z : R) (p : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (faithful : ∀ a b : BitStr, a.length = p.length → b.length = p.length →
      (BinaryPolynomial.evalBits z a = BinaryPolynomial.evalBits z b ↔ a = b))
    (φ β : BitStr) (hφ : φ.length = p.length) (hβ : β.length = p.length)
    (lits certs : List (BitStr × BitStr)) (hl : CorrectPairs p lits) (hc : CorrectPairs p certs) :
    checksProg (p, φ, β, lits, certs) = true ↔
      BinaryPolynomial.evalBits z β = BinaryPolynomial.evalBits z φ *
        (lits.map (fun a => BinaryPolynomial.evalBits z a.1 - BinaryPolynomial.evalBits z a.2)).prod ∧
      BinaryPolynomial.evalBits z β =
        (certs.map (fun a => BinaryPolynomial.evalBits z a.1 *
          (BinaryPolynomial.evalBits z a.2 * (1 - BinaryPolynomial.evalBits z a.2)))).sum := by
  rw [checksProg_apply, checks, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    ← faithful β (formulaValue p φ lits) hβ (length_formulaValue p φ lits hφ),
    ← faithful β (certificateValue p certs) hβ (length_certificateValue p certs hc),
    eval_formulaValue z p hp hroot φ hφ lits hl, eval_certificateValue z p hp hroot certs hc]
end
end MIPRE.SAT.PcpFieldTests

namespace MIPRE.SAT.Circuit
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial Finset
theorem fieldPrefix_env (C : Circuit) (p : BitStr) (x w : List BitStr) (k : ℕ) :
    (C.fieldPrefix p x w k).1 = (p, x, w, C.fieldHistory w k) := by
  simpa [fieldPrefix] using
    (fold_fieldStep (C.fieldHistory w k) ((p, x, w, []), oneBits p)).1
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial Finset
theorem fieldPrefix_succ (C : Circuit) (p : BitStr) (x w : List BitStr) (k : ℕ) :
    C.fieldPrefix p x w (k + 1) =
      fieldStep (C.fieldPrefix p x w k) (C.gates.getD k (.const false), w.getD k []) := by
  simp only [fieldPrefix, fieldHistory, List.range_succ, List.map_append,
    List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial Finset
theorem fieldPrefix_width (C : Circuit) (p : BitStr) (x w : List BitStr) (k : ℕ) :
    (C.fieldPrefix p x w k).2.length = p.length := by
  induction k with
  | zero => exact length_oneBits p
  | succ k ih =>
    rw [fieldPrefix_succ]
    change (mulReduce _ _ _).length = p.length
    rw [show (C.fieldPrefix p x w k).1.1 = p from
      congrArg Prod.fst (fieldPrefix_env C p x w k)]
    exact length_mulReduce _ _ _ ih
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial Finset
variable {F : Type*} [Field F] [CharP F 2]
/-- The evaluator always returns the supplied modulus width. -/
theorem length_circuitBits (C : Circuit) (p : BitStr) (x w : List BitStr) :
    (circuitBits p x w C.gates).length = p.length :=
  length_mulReduce p _ _ (fieldPrefix_width C p x w C.size)
end
end MIPRE.SAT.Circuit

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

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc LowDegree LowDegree.BinaryPolynomial
set_option maxRecDepth 4096
theorem verifierLiterals_apply (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    verifierLiterals (pcpInput D n T Q σ x y z ev) =
      (ev.take 5).zip ((z.drop (5 * (pcpParams n T Q σ).m)).take 5) := by
  simp only [verifierLiterals, comp_apply, pair_apply, zip_apply, take_apply, drop_apply,
    claimsProg, pointProg, fst_apply, snd_apply, const_apply, length_unary, length_nsmulU,
    innerDimParamsU_length, verifierParams, pcpInput, pcpParams]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc LowDegree LowDegree.BinaryPolynomial
set_option maxRecDepth 4096
theorem verifierCertificates_apply (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    verifierCertificates (pcpInput D n T Q σ x y z ev) = (ev.drop 6).zip z := by
  simp only [verifierCertificates, comp_apply, pair_apply, zip_apply, drop_apply,
    claimsProg, pointProg, fst_apply, snd_apply, const_apply, length_unary, pcpInput]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc LowDegree LowDegree.BinaryPolynomial
set_option maxRecDepth 4096
theorem verifierTests_apply (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    verifierTests (pcpInput D n T Q σ x y z ev) =
      PcpFieldTests.checksProg
        (verifierModulus (pcpInput D n T Q σ x y z ev),
          verifierCircuitValue (pcpInput D n T Q σ x y z ev), ev.getD 5 [],
          (ev.take 5).zip ((z.drop (5 * (pcpParams n T Q σ).m)).take 5), (ev.drop 6).zip z) := by
  change PcpFieldTests.checksProg
    (verifierModulus (pcpInput D n T Q σ x y z ev),
      verifierCircuitValue (pcpInput D n T Q σ x y z ev), ev.getD 5 [],
      verifierLiterals (pcpInput D n T Q σ x y z ev),
      verifierCertificates (pcpInput D n T Q σ x y z ev)) = _
  rw [verifierLiterals_apply, verifierCertificates_apply]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.SAT.BinField
section
open Cost LowDegree LowDegree.BinaryPolynomial
variable {k : ℕ} (E : BinField k)
/-- Slicing the raw blocks is exactly slicing the typed coordinate function. -/
theorem slice_vecBits {n : ℕ} (v : Fin n → E.carrier) (a b : ℕ) (h : a + b ≤ n) :
    ((E.vecBits v).drop a).take b =
      E.vecBits (fun i : Fin b => v ⟨a + i, by have := i.isLt; omega⟩) := by
  simp only [vecBits_eq_ofFn]
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
end
end MIPRE.SAT.BinField

namespace MIPRE.SAT.BinField
section
open Cost LowDegree LowDegree.BinaryPolynomial
variable {k : ℕ} (E : BinField k)
theorem zip_vecBits {n : ℕ} (v w : Fin n → E.carrier) :
    (E.vecBits v).zip (E.vecBits w) =
      List.ofFn (fun i => (E.toBits (v i), E.toBits (w i))) := by
  simp only [vecBits_eq_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zip, List.getElem_ofFn]
end
end MIPRE.SAT.BinField

namespace MIPRE.SAT.PcpViewTests
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial
variable {k : ℕ} (E : BinField k) (P : PcpParams)
theorem main_claim (α : Fin 5 → E.carrier) (β : Fin (P.m' + 1) → E.carrier) :
    (E.vecBits α ++ E.vecBits β).getD 5 [] = E.toBits (β 0) := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp), E.length_vecBits, Nat.sub_self]
  exact E.getD_vecBits β 0
end
end MIPRE.SAT.PcpViewTests

namespace MIPRE.SAT.PcpViewTests
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial
variable {k : ℕ} (E : BinField k) (P : PcpParams)
theorem tail_claims (α : Fin 5 → E.carrier) (β : Fin (P.m' + 1) → E.carrier) :
    (E.vecBits α ++ E.vecBits β).drop 6 = E.vecBits (fun i : Fin P.m' => β i.succ) := by
  have ha : (E.vecBits α).drop 6 = [] := List.drop_eq_nil_of_le (by simp)
  have hb : E.vecBits β = E.toBits (β 0) :: E.vecBits (fun i : Fin P.m' => β i.succ) := by
    rw [E.vecBits_eq_ofFn, List.ofFn_succ, E.vecBits_eq_ofFn]
  rw [List.drop_append, ha, List.nil_append, E.length_vecBits]
  simpa only [hb, List.drop_succ_cons, List.drop_zero]
end
end MIPRE.SAT.PcpViewTests

namespace MIPRE.SAT.PcpViewTests
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial
variable {k : ℕ} (E : BinField k) (P : PcpParams)
theorem literals_vecBits (z : Fin P.m' → E.carrier)
    (α : Fin 5 → E.carrier) (β : Fin (P.m' + 1) → E.carrier) :
    literals P (E.vecBits z) (E.vecBits α ++ E.vecBits β) =
      List.ofFn (fun i => (E.toBits (α i), E.toBits (z (P.signIndex i)))) := by
  rw [literals, List.take_left' (E.length_vecBits α)]
  have hs := E.slice_vecBits z (5 * P.m) 5 (by unfold PcpParams.m'; omega)
  rw [hs]
  exact E.zip_vecBits α (fun i => z (P.signIndex i))
end
end MIPRE.SAT.PcpViewTests

namespace MIPRE.SAT.PcpViewTests
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial
variable {k : ℕ} (E : BinField k) (P : PcpParams)
theorem certificates_vecBits (z : Fin P.m' → E.carrier)
    (α : Fin 5 → E.carrier) (β : Fin (P.m' + 1) → E.carrier) :
    certificates (E.vecBits z) (E.vecBits α ++ E.vecBits β) =
      List.ofFn (fun i : Fin P.m' => (E.toBits (β i.succ), E.toBits (z i))) := by
  rw [certificates, tail_claims E P]
  exact E.zip_vecBits _ _
end
end MIPRE.SAT.PcpViewTests

namespace MIPRE.SAT.PcpViewTests
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial
variable {k : ℕ} (E : BinField k) (P : PcpParams)
theorem correctPairs_ofFn (p : BitStr) (hpk : p.length = k) {n : ℕ}
    (a b : Fin n → E.carrier) :
    PcpFieldTests.CorrectPairs p (List.ofFn (fun i => (E.toBits (a i), E.toBits (b i)))) := by
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact ⟨(E.length_toBits _).trans hpk.symm, (E.length_toBits _).trans hpk.symm⟩
end
end MIPRE.SAT.PcpViewTests

namespace MIPRE.SAT.PcpViewTests
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial
variable {k : ℕ} (E : BinField k) (P : PcpParams)
/-- On a typed view with canonical coefficient decoding, the executable tests
are exactly `TypedAccepts`, including the order of all certificate coordinates. -/
theorem checks_typed_iff [CharP E.carrier 2] (root : E.carrier)
    (p : BitStr) (hp : p ≠ []) (hpk : p.length = k)
    (hroot : root ^ p.length = BinaryPolynomial.evalBits root p)
    (hencode : ∀ a : E.carrier, BinaryPolynomial.evalBits root (E.toBits a) = a)
    (faithful : ∀ a b : BitStr, a.length = p.length → b.length = p.length →
      (BinaryPolynomial.evalBits root a = BinaryPolynomial.evalBits root b ↔ a = b))
    (Φ : MvPolynomial (Fin P.m') E.carrier) (z : Fin P.m' → E.carrier)
    (φ : BitStr) (hφ : φ.length = p.length) (hφeval : BinaryPolynomial.evalBits root φ = eval z Φ)
    (α : Fin 5 → E.carrier) (β : Fin (P.m' + 1) → E.carrier) :
    PcpFieldTests.checksProg (p, φ, (E.vecBits α ++ E.vecBits β).getD 5 [],
      literals P (E.vecBits z) (E.vecBits α ++ E.vecBits β),
      certificates (E.vecBits z) (E.vecBits α ++ E.vecBits β)) = true ↔
        PcpAlgebra.TypedAccepts Φ z (α, β) := by
  rw [main_claim E P, literals_vecBits E P, certificates_vecBits E P]
  rw [PcpFieldTests.checksProg_true_iff root p hp hroot faithful φ (E.toBits (β 0)) hφ
    ((E.length_toBits _).trans hpk.symm) _ _
    (correctPairs_ofFn E p hpk _ _) (correctPairs_ofFn E p hpk _ _)]
  simp only [List.map_ofFn, List.prod_ofFn, List.sum_ofFn, Function.comp_apply, hencode, hφeval,
    PcpAlgebra.TypedAccepts]
end
end MIPRE.SAT.PcpViewTests

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
    (faithful : ∀ a b : BitStr, a.length = (pcpParams n T Q σ).k →
      b.length = (pcpParams n T Q σ).k →
      (BinaryPolynomial.evalBits root a = BinaryPolynomial.evalBits root b ↔ a = b))
    (z : Fin (pcpParams n T Q σ).m' → E.carrier)
    (α : Fin 5 → E.carrier) (β : Fin ((pcpParams n T Q σ).m' + 1) → E.carrier) :
    verifierTests (pcpInput D n T Q σ x y (E.vecBits z) (E.vecBits α ++ E.vecBits β)) = true ↔
      PcpAlgebra.TypedAccepts (clausePolynomial D n T Q σ x y hV) z (α, β) := by
  have hp := pcpModulus_length n T Q σ
  have hf := viewFormat_typed (pcpParams n T Q σ) E z α β
  rw [verifierTests_apply, verifierModulus_apply]
  apply PcpViewTests.checks_typed_iff E (pcpParams n T Q σ) root
    (pcpModulus n T Q σ) (pcpModulus_ne_nil n T Q σ) hp hroot hencode
    (fun a b ha hb => faithful a b (ha.trans hp) (hb.trans hp))
  · rw [verifierCircuitValue_apply, verifierModulus_apply,
      pcpCircuitProg_eq_fixed D n T Q σ x y _ _ hf]
    exact Circuit.length_circuitBits (fixedCircuit D n T Q σ x y) _ _ _
  · exact verifierCircuitValue_typed D n T Q σ x y hV E root hroot hencode z α β
end MIPRE.TM.CookLevin.Pad

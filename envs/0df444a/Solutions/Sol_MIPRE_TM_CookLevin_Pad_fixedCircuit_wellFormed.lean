-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Pad.fixedCircuit_wellFormed
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:28:36.41786+00:00
-- url     : https://prove2.me/submissions/6ee1b42d-3b90-418b-b6a5-aa21ae9bdbc3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/PcpBridge.lean (solution of MIPRE.TM.CookLevin.Pad.fixedCircuit_wellFormed);
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
import Theorems.Thm_MIPRE_SAT_Circuit_wellFormed_copyOutput
import Theorems.Thm_MIPRE_SAT_Fml_toCircuit_wellFormed
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_InputsLt_linkFml
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_litFields_inputsLt
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_nbitsR_apply
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_formula_inputsLt

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.xnor {n : ℕ} {f g : Fml} (hf : f.InputsLt n) (hg : g.InputsLt n) :
    (Fml.xnor f g).InputsLt n := ⟨⟨hf, hg⟩, hf, hg⟩
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.xor {n : ℕ} {f g : Fml} (hf : f.InputsLt n) (hg : g.InputsLt n) :
    (Fml.xor f g).InputsLt n := ⟨⟨hf, hg⟩, hf, hg⟩
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.mux {n : ℕ} {s a b : Fml} (hs : s.InputsLt n) (ha : a.InputsLt n) (hb : b.InputsLt n) :
    (Fml.mux s a b).InputsLt n := ⟨⟨hs, ha⟩, hs, hb⟩
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.foldl_and {n : ℕ} (l : List Fml) (init : Fml) (hi : init.InputsLt n)
    (hl : ∀ f ∈ l, f.InputsLt n) : (l.foldl and init).InputsLt n := by
  induction l generalizing init with
  | nil => exact hi
  | cons f l ih =>
    exact ih (and init f) ⟨hi, hl f (List.mem_cons_self ..)⟩ fun g hg => hl g (List.mem_cons_of_mem _ hg)
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.andList {n : ℕ} (l : List Fml) (hl : ∀ f ∈ l, f.InputsLt n) : (Fml.andList l).InputsLt n :=
  InputsLt.foldl_and l _ trivial hl
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.foldl_or {n : ℕ} (l : List Fml) (init : Fml) (hi : init.InputsLt n)
    (hl : ∀ f ∈ l, f.InputsLt n) : (l.foldl or init).InputsLt n := by
  induction l generalizing init with
  | nil => exact hi
  | cons f l ih =>
    exact ih (or init f) ⟨hi, hl f (List.mem_cons_self ..)⟩ fun g hg => hl g (List.mem_cons_of_mem _ hg)
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.orList {n : ℕ} (l : List Fml) (hl : ∀ f ∈ l, f.InputsLt n) : (Fml.orList l).InputsLt n :=
  InputsLt.foldl_or l _ trivial hl
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.foldl_zip {n : ℕ} {γ : Type*} (step : Fml → Fml × γ → Fml)
    (hstep : ∀ acc p, acc.InputsLt n → p.1.InputsLt n → (step acc p).InputsLt n)
    (fs : List Fml) (c : List γ) (init : Fml) (hi : init.InputsLt n) (hl : ∀ f ∈ fs, f.InputsLt n) :
    ((fs.zip c).foldl step init).InputsLt n := by
  induction fs generalizing c init with
  | nil => exact hi
  | cons f fs ih =>
    cases c with
    | nil => exact hi
    | cons b c =>
      rw [List.zip_cons_cons, List.foldl_cons]
      exact ih c _ (hstep init (f, b) hi (hl f (List.mem_cons_self ..)))
        fun g hg => hl g (List.mem_cons_of_mem _ hg)
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.eqConst {n : ℕ} {fs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n) :
    (Fml.eqConst fs c).InputsLt n :=
  InputsLt.foldl_zip Fml.eqStep (fun acc p ha hp => ⟨ha, by show InputsLt _ (if p.2 then p.1 else not p.1); split <;> exact hp⟩)
    fs c _ trivial h
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.foldl_zip₂ {n : ℕ} (step : Fml → Fml × Fml → Fml)
    (hstep : ∀ acc p, acc.InputsLt n → p.1.InputsLt n → p.2.InputsLt n → (step acc p).InputsLt n)
    (fs gs : List Fml) (init : Fml) (hi : init.InputsLt n) (hf : ∀ f ∈ fs, f.InputsLt n)
    (hg : ∀ f ∈ gs, f.InputsLt n) : ((fs.zip gs).foldl step init).InputsLt n := by
  induction fs generalizing gs init with
  | nil => exact hi
  | cons f fs ih =>
    cases gs with
    | nil => exact hi
    | cons g gs =>
      rw [List.zip_cons_cons, List.foldl_cons]
      exact ih gs _ (hstep init (f, g) hi (hf f (List.mem_cons_self ..)) (hg g (List.mem_cons_self ..)))
        (fun x hx => hf x (List.mem_cons_of_mem _ hx)) fun x hx => hg x (List.mem_cons_of_mem _ hx)
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.eqFields {n : ℕ} {fs gs : List Fml} (h : ∀ f ∈ fs, f.InputsLt n)
    (hg : ∀ f ∈ gs, f.InputsLt n) : (Fml.eqFields fs gs).InputsLt n :=
  InputsLt.foldl_zip₂ Fml.eqFStep (fun _ _ ha hp hq => ⟨ha, hp.xnor hq⟩) fs gs _ trivial h hg
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.ltConst {n : ℕ} {fs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n) :
    (Fml.ltConst fs c).InputsLt n :=
  InputsLt.foldl_zip Fml.ltStep (fun _ _ ha hp => ⟨⟨hp, trivial⟩, hp.xnor trivial, ha⟩) fs c _ trivial h
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.ltFields {n : ℕ} {fs gs : List Fml} (h : ∀ f ∈ fs, f.InputsLt n)
    (hg : ∀ f ∈ gs, f.InputsLt n) : (Fml.ltFields fs gs).InputsLt n :=
  InputsLt.foldl_zip₂ Fml.ltFStep (fun _ _ ha hp hq => ⟨⟨hp, hq⟩, hp.xnor hq, ha⟩) fs gs _ trivial h hg
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.sum3 {n : ℕ} {f b c : Fml} (hf : f.InputsLt n) (hb : b.InputsLt n) (hc : c.InputsLt n) :
    (Fml.sum3 f b c).InputsLt n := (hf.xor hb).xor hc
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.maj3 {n : ℕ} {f b c : Fml} (hf : f.InputsLt n) (hb : b.InputsLt n) (hc : c.InputsLt n) :
    (Fml.maj3 f b c).InputsLt n := ⟨⟨hf, hb⟩, ⟨hf, hb⟩, hc⟩
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.addBits {n : ℕ} : ∀ (fs : List Fml) (c : BitStr) (cin : Fml),
    (∀ f ∈ fs, f.InputsLt n) → cin.InputsLt n →
    (∀ f ∈ (Fml.addBits fs c cin).1, f.InputsLt n) ∧ (Fml.addBits fs c cin).2.InputsLt n
  | f :: fs, b :: c, cin, hf, hc => by
    have hf0 : f.InputsLt n := hf f (List.mem_cons_self ..)
    have ih := InputsLt.addBits fs c (Fml.maj3 f (const b) cin)
      (fun g hg => hf g (List.mem_cons_of_mem _ hg))
      (InputsLt.maj3 (b := const b) hf0 trivial hc)
    refine ⟨?_, ih.2⟩
    intro g hg
    simp only [Fml.addBits, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact InputsLt.sum3 (b := const b) hf0 trivial hc
    · exact ih.1 g hg
  | [], _, cin, _, hc => ⟨fun g hg => absurd hg List.not_mem_nil, hc⟩
  | _ :: _, [], cin, _, hc => ⟨fun g hg => absurd hg List.not_mem_nil, hc⟩
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.addConstBits {n : ℕ} {fs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n) :
    ∀ f ∈ Fml.addConstBits fs c, f.InputsLt n :=
  (InputsLt.addBits fs c (const false) h (trivial : (const false).InputsLt n)).1
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.addConstCarry {n : ℕ} {fs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n) :
    (Fml.addConstCarry fs c).InputsLt n :=
  (InputsLt.addBits fs c (const false) h (trivial : (const false).InputsLt n)).2
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.addConstRel {n : ℕ} {fs gs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n)
    (hg : ∀ f ∈ gs, f.InputsLt n) : (Fml.addConstRel fs gs c).InputsLt n :=
  ⟨InputsLt.eqFields hg (InputsLt.addConstBits c h), InputsLt.addConstCarry c h⟩
end
end MIPRE.SAT.Fml

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.and' {n : ℕ} {f g : Fml} (hf : f.InputsLt n) (hg : g.InputsLt n) :
    (Fml.and f g).InputsLt n := ⟨hf, hg⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.or' {n : ℕ} {f g : Fml} (hf : f.InputsLt n) (hg : g.InputsLt n) :
    (Fml.or f g).InputsLt n := ⟨hf, hg⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.not' {n : ℕ} {f : Fml} (hf : f.InputsLt n) : (Fml.not f).InputsLt n := hf
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.list_cons {n : ℕ} {f : Fml} {l : List Fml} (hf : f.InputsLt n) (hl : ∀ g ∈ l, g.InputsLt n) :
    ∀ g ∈ f :: l, g.InputsLt n := by
  simpa [List.forall_mem_cons] using ⟨hf, hl⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.list_nil {n : ℕ} : ∀ g ∈ ([] : List Fml), g.InputsLt n := by simp
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable {e G n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA
theorem InputsLt.isCellF : (isCellF e A).InputsLt n :=
  InputsLt.or' (InputsLt.andList _ (InputsLt.list_cons hA.flag (InputsLt.list_cons (InputsLt.eqConst _ hA.tag)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.t) (InputsLt.list_cons (InputsLt.ltConst _ hA.d)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.p) (InputsLt.list_cons (InputsLt.ltConst _ hA.v) InputsLt.list_nil)))))))
    (InputsLt.andList _ (InputsLt.list_cons (InputsLt.not' hA.flag) (InputsLt.list_cons hA.ansOk
    (InputsLt.list_cons (InputsLt.eqConst _ hA.tag) (InputsLt.list_cons (InputsLt.eqConst _ hA.t)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.d) (InputsLt.list_cons (InputsLt.ltConst _ hA.p)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.v) InputsLt.list_nil))))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable {e G n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA
theorem InputsLt.isHeadF : (isHeadF e A).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons hA.flag (InputsLt.list_cons (InputsLt.eqConst _ hA.tag)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.t) (InputsLt.list_cons (InputsLt.ltConst _ hA.d)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.p) InputsLt.list_nil)))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable {e G n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA
theorem InputsLt.isStateF : (isStateF e A).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons hA.flag (InputsLt.list_cons (InputsLt.eqConst _ hA.tag)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.t) (InputsLt.list_cons (InputsLt.ltConst _ hA.q) InputsLt.list_nil))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable {e G n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA
theorem InputsLt.isEmitOneF : (isEmitOneF e A).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons hA.flag (InputsLt.list_cons (InputsLt.eqConst _ hA.tag)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.t) InputsLt.list_nil)))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable {e G n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA
theorem InputsLt.isEmitBadF : (isEmitBadF e A).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons hA.flag (InputsLt.list_cons (InputsLt.eqConst _ hA.tag)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.t) InputsLt.list_nil)))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable {e G n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA
theorem InputsLt.isEmittedF : (isEmittedF e A).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons hA.flag (InputsLt.list_cons (InputsLt.eqConst _ hA.tag)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.t) InputsLt.list_nil)))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable {e G n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA
theorem InputsLt.isAuxF : (isAuxF e G A).InputsLt n := by
  refine InputsLt.andList _ ?_
  intro f hf
  rw [List.mem_append, List.mem_ofFn] at hf
  rcases hf with hf | ⟨k, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact hA.flag
    · exact InputsLt.eqConst _ hA.tag
    · exact InputsLt.ltConst _ hA.t
    · exact InputsLt.ltConst _ hA.g
  · exact InputsLt.ltConst _ (hA.js k)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {A B : FieldsF} (hA : A.InputsLt n) (hB : B.InputsLt n)
include hA hB
theorem InputsLt.cellEqF : (cellEqF A B).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hA.t hB.t) (InputsLt.list_cons (InputsLt.eqFields hA.d hB.d)
    (InputsLt.list_cons (InputsLt.eqFields hA.p hB.p) (InputsLt.list_cons (InputsLt.eqFields hA.v hB.v) InputsLt.list_nil))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {A B : FieldsF} (hA : A.InputsLt n) (hB : B.InputsLt n)
include hA hB
theorem InputsLt.headEqF : (headEqF A B).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hA.t hB.t) (InputsLt.list_cons (InputsLt.eqFields hA.d hB.d)
    (InputsLt.list_cons (InputsLt.eqFields hA.p hB.p) InputsLt.list_nil)))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {A B : FieldsF} (hA : A.InputsLt n) (hB : B.InputsLt n)
include hA hB
theorem InputsLt.stateEqF : (stateEqF A B).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hA.t hB.t)
    (InputsLt.list_cons (InputsLt.eqFields hA.q hB.q) InputsLt.list_nil))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {A B : FieldsF} (hA : A.InputsLt n) (hB : B.InputsLt n)
include hA hB
theorem InputsLt.samePosF : (samePosF A B).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hA.t hB.t) (InputsLt.list_cons (InputsLt.eqFields hA.d hB.d)
    (InputsLt.list_cons (InputsLt.eqFields hA.p hB.p) InputsLt.list_nil)))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {A B : FieldsF} (hA : A.InputsLt n) (hB : B.InputsLt n)
include hA hB
theorem InputsLt.tEqF : (eqFields A.t B.t).InputsLt n := InputsLt.eqFields hA.t hB.t
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {A B : FieldsF} (hA : A.InputsLt n) (hB : B.InputsLt n)
include hA hB
theorem InputsLt.auxEqF : (auxEqF A B).InputsLt n := by
  refine InputsLt.andList _ ?_
  intro f hf
  rw [List.mem_append, List.mem_ofFn] at hf
  rcases hf with hf | ⟨k, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact InputsLt.eqFields hA.t hB.t
    · exact InputsLt.eqFields hA.g hB.g
  · exact InputsLt.eqFields (hA.js k) (hB.js k)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.unitCellF : (unitCellF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isCellF hC.A₁) (InputsLt.list_cons (InputsLt.isCellF hC.A₂)
    (InputsLt.list_cons (InputsLt.isCellF hC.A₃) (InputsLt.list_cons (InputsLt.cellEqF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.cellEqF hC.A₁ hC.A₃) InputsLt.list_nil)))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.unitHeadF : (unitHeadF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isHeadF hC.A₁) (InputsLt.list_cons (InputsLt.isHeadF hC.A₂)
    (InputsLt.list_cons (InputsLt.isHeadF hC.A₃) (InputsLt.list_cons (InputsLt.headEqF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.headEqF hC.A₁ hC.A₃) InputsLt.list_nil)))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.unitStateF : (unitStateF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isStateF hC.A₁) (InputsLt.list_cons (InputsLt.isStateF hC.A₂)
    (InputsLt.list_cons (InputsLt.isStateF hC.A₃) (InputsLt.list_cons (InputsLt.stateEqF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.stateEqF hC.A₁ hC.A₃) InputsLt.list_nil)))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.unitEmitBadF : (unitEmitBadF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmitBadF hC.A₁) (InputsLt.list_cons (InputsLt.isEmitBadF hC.A₂)
    (InputsLt.list_cons (InputsLt.isEmitBadF hC.A₃) (InputsLt.list_cons (InputsLt.tEqF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.tEqF hC.A₁ hC.A₃) InputsLt.list_nil)))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.unitEmittedF : (unitEmittedF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmittedF hC.A₁) (InputsLt.list_cons (InputsLt.isEmittedF hC.A₂)
    (InputsLt.list_cons (InputsLt.isEmittedF hC.A₃) (InputsLt.list_cons (InputsLt.tEqF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.tEqF hC.A₁ hC.A₃) InputsLt.list_nil)))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.unitAuxF : (unitAuxF e G C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isAuxF hC.A₁) (InputsLt.list_cons (InputsLt.isAuxF hC.A₂)
    (InputsLt.list_cons (InputsLt.isAuxF hC.A₃) (InputsLt.list_cons (InputsLt.auxEqF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.auxEqF hC.A₁ hC.A₃) InputsLt.list_nil)))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.sameSignsF : (sameSignsF C).InputsLt n :=
  InputsLt.and' (InputsLt.xnor hC.σ₂ hC.σ₁) (InputsLt.xnor hC.σ₃ hC.σ₁)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA
theorem InputsLt.bdryF : (bdryF e A).InputsLt n :=
  InputsLt.or' (InputsLt.ltConst _ hA.p) (InputsLt.not' (InputsLt.ltConst _ hA.p))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA
theorem InputsLt.startCellF : (startCellF e A).InputsLt n :=
  InputsLt.mux (InputsLt.ltConst _ hA.d) (InputsLt.eqConst _ hA.p) (InputsLt.eqConst _ hA.p)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA
theorem InputsLt.workValF : (workValF e A).InputsLt n :=
  InputsLt.mux (InputsLt.bdryF e hA) (InputsLt.eqConst _ hA.v) (InputsLt.eqConst _ hA.v)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA
theorem InputsLt.lookupList (codes : List ℕ) : ∀ k, ∀ f ∈ lookupList e A k codes, f.InputsLt n := by
  induction codes with
  | nil => intro k f hf; simp [Desc.lookupList] at hf
  | cons c cs ih =>
    intro k f hf
    simp only [Desc.lookupList, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact InputsLt.and' (InputsLt.eqConst _ hA.p) (InputsLt.eqConst _ hA.v)
    · exact ih _ f hf
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA
theorem InputsLt.cellValF (codes : List ℕ) : (cellValF e A codes).InputsLt n :=
  InputsLt.mux (InputsLt.bdryF e hA) (InputsLt.eqConst _ hA.v)
    (InputsLt.mux (InputsLt.and' (InputsLt.not' (InputsLt.ltConst _ hA.p)) (InputsLt.ltConst _ hA.p))
      (InputsLt.orList _ (InputsLt.lookupList e hA codes 3)) (InputsLt.eqConst _ hA.v))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA
theorem InputsLt.unaryValF (T : ℕ) : (unaryValF e T A).InputsLt n :=
  InputsLt.mux (InputsLt.bdryF e hA) (InputsLt.eqConst _ hA.v)
    (InputsLt.mux (InputsLt.and' (InputsLt.not' (InputsLt.ltConst _ hA.p)) (InputsLt.ltConst _ hA.p))
      (InputsLt.eqConst _ hA.v) (InputsLt.eqConst _ hA.v))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
theorem InputsLt.freeTapeF {n : ℕ} (frees : List ℕ) {A : FieldsF} (hA : A.InputsLt n) :
    (freeTapeF frees A).InputsLt n := by
  refine InputsLt.orList _ ?_
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨j, -, rfl⟩ := hf
  exact InputsLt.eqConst _ hA.d
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
theorem InputsLt.tZeroF {n : ℕ} {A : FieldsF} (hA : A.InputsLt n) : (tZeroF e A).InputsLt n :=
  InputsLt.eqConst _ hA.t
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} (tabs : List (ℕ × Fml)) (htabs : ∀ jv ∈ tabs, jv.2.InputsLt n) {C : CandF}
  (hC : C.InputsLt n)
include hC
theorem InputsLt.startHeadF : (startHeadF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitHeadF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.xnor hC.σ₁ (InputsLt.startCellF e hC.A₁))
    InputsLt.list_nil))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} (tabs : List (ℕ × Fml)) (htabs : ∀ jv ∈ tabs, jv.2.InputsLt n) {C : CandF}
  (hC : C.InputsLt n)
include hC
theorem InputsLt.startStateF : (startStateF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitStateF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.xnor hC.σ₁ (InputsLt.eqConst _ hC.A₁.q))
    InputsLt.list_nil))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} (tabs : List (ℕ × Fml)) (htabs : ∀ jv ∈ tabs, jv.2.InputsLt n) {C : CandF}
  (hC : C.InputsLt n)
include hC
include htabs in
theorem InputsLt.startFixedF : (startFixedF e tabs C).InputsLt n := by
  refine InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons ?_ InputsLt.list_nil))))
  refine InputsLt.orList _ ?_
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨jv, hjv, rfl⟩ := hf
  exact InputsLt.and' (InputsLt.eqConst _ hC.A₁.d) (InputsLt.xnor hC.σ₁ (htabs jv hjv))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} (tabs : List (ℕ × Fml)) (htabs : ∀ jv ∈ tabs, jv.2.InputsLt n) {C : CandF}
  (hC : C.InputsLt n)
include hC
theorem InputsLt.startWorkF : (startWorkF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.not' (InputsLt.ltConst _ hC.A₁.d))
    (InputsLt.list_cons (InputsLt.xnor hC.σ₁ (InputsLt.workValF e hC.A₁)) InputsLt.list_nil)))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} (tabs : List (ℕ × Fml)) (htabs : ∀ jv ∈ tabs, jv.2.InputsLt n) {C : CandF}
  (hC : C.InputsLt n)
include hC
include htabs in
theorem InputsLt.startF : (startF e tabs C).InputsLt n :=
  InputsLt.orList _ (InputsLt.list_cons (InputsLt.startHeadF e hC) (InputsLt.list_cons (InputsLt.startStateF e hC)
    (InputsLt.list_cons (InputsLt.startFixedF e tabs htabs hC) (InputsLt.list_cons (InputsLt.startWorkF e hC)
    InputsLt.list_nil))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} (frees : List ℕ) {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.freeBdryF : (freeBdryF e frees C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.freeTapeF frees hC.A₁)
    (InputsLt.list_cons (InputsLt.bdryF e hC.A₁) (InputsLt.list_cons (InputsLt.xnor hC.σ₁ (InputsLt.eqConst _ hC.A₁.v))
    InputsLt.list_nil))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} (frees : List ℕ) {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.freeOtherF : (freeOtherF e frees C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.freeTapeF frees hC.A₁)
    (InputsLt.list_cons (InputsLt.not' (InputsLt.bdryF e hC.A₁))
    (InputsLt.list_cons (InputsLt.not' (InputsLt.eqConst _ hC.A₁.v))
    (InputsLt.list_cons (InputsLt.not' (InputsLt.eqConst _ hC.A₁.v))
    (InputsLt.list_cons (InputsLt.not' (InputsLt.eqConst _ hC.A₁.v))
    (InputsLt.list_cons (InputsLt.not' hC.σ₁) InputsLt.list_nil)))))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} (frees : List ℕ) {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.freeTwoF : (freeTwoF e frees C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.freeTapeF frees hC.A₁)
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.p)
    (InputsLt.list_cons (InputsLt.xnor hC.σ₁ (InputsLt.eqConst _ hC.A₁.v)) InputsLt.list_nil))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} (frees : List ℕ) {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.freeOneOfF : (freeOneOfF e frees C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isCellF hC.A₁) (InputsLt.list_cons (InputsLt.isCellF hC.A₂)
    (InputsLt.list_cons (InputsLt.isCellF hC.A₃) (InputsLt.list_cons (InputsLt.samePosF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.samePosF hC.A₁ hC.A₃) (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁)
    (InputsLt.list_cons (InputsLt.freeTapeF frees hC.A₁) (InputsLt.list_cons (InputsLt.not' (InputsLt.bdryF e hC.A₁))
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.v) (InputsLt.list_cons (InputsLt.eqConst _ hC.A₂.v)
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₃.v) (InputsLt.list_cons hC.σ₁ (InputsLt.list_cons hC.σ₂
    (InputsLt.list_cons hC.σ₃ InputsLt.list_nil))))))))))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} (frees : List ℕ) {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.freeNandF : (freeNandF e frees C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isCellF hC.A₁) (InputsLt.list_cons (InputsLt.isCellF hC.A₂)
    (InputsLt.list_cons (InputsLt.isCellF hC.A₃) (InputsLt.list_cons (InputsLt.samePosF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.cellEqF hC.A₂ hC.A₃) (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁)
    (InputsLt.list_cons (InputsLt.freeTapeF frees hC.A₁) (InputsLt.list_cons (InputsLt.not' (InputsLt.bdryF e hC.A₁))
    (InputsLt.list_cons (InputsLt.not' (InputsLt.eqFields hC.A₁.v hC.A₂.v))
    (InputsLt.list_cons (InputsLt.not' hC.σ₁) (InputsLt.list_cons (InputsLt.not' hC.σ₂)
    (InputsLt.list_cons (InputsLt.not' hC.σ₃) InputsLt.list_nil))))))))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} (frees : List ℕ) {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.freeBlankF : (freeBlankF e frees C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isCellF hC.A₁) (InputsLt.list_cons (InputsLt.isCellF hC.A₂)
    (InputsLt.list_cons (InputsLt.isCellF hC.A₃) (InputsLt.list_cons (InputsLt.cellEqF hC.A₂ hC.A₃)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.freeTapeF frees hC.A₁)
    (InputsLt.list_cons (InputsLt.eqFields hC.A₂.t hC.A₁.t) (InputsLt.list_cons (InputsLt.eqFields hC.A₂.d hC.A₁.d)
    (InputsLt.list_cons (InputsLt.not' (InputsLt.ltConst _ hC.A₁.p)) (InputsLt.list_cons (InputsLt.not' (InputsLt.bdryF e hC.A₂))
    (InputsLt.list_cons (InputsLt.ltFields hC.A₁.p hC.A₂.p) (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.v)
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₂.v) (InputsLt.list_cons (InputsLt.not' hC.σ₁)
    (InputsLt.list_cons hC.σ₂ (InputsLt.list_cons hC.σ₃ InputsLt.list_nil))))))))))))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} (frees : List ℕ) {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.freeF : (freeF e frees C).InputsLt n :=
  InputsLt.orList _ (InputsLt.list_cons (InputsLt.freeBdryF e frees hC) (InputsLt.list_cons (InputsLt.freeOtherF e frees hC)
    (InputsLt.list_cons (InputsLt.freeTwoF e frees hC) (InputsLt.list_cons (InputsLt.freeOneOfF e frees hC)
    (InputsLt.list_cons (InputsLt.freeNandF e frees hC) (InputsLt.list_cons (InputsLt.freeBlankF e frees hC)
    InputsLt.list_nil))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.bdryCellF : (bdryCellF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.bdryF e hC.A₁) (InputsLt.list_cons (InputsLt.xnor hC.σ₁ (InputsLt.eqConst _ hC.A₁.v))
    InputsLt.list_nil))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.bdryHeadF : (bdryHeadF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitHeadF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.bdryF e hC.A₁) (InputsLt.list_cons (InputsLt.not' hC.σ₁) InputsLt.list_nil))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.bdryPredF : (bdryPredF e C).InputsLt n :=
  InputsLt.or' (InputsLt.bdryCellF e hC) (InputsLt.bdryHeadF e hC)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.emitZeroF : (emitZeroF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitEmittedF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.not' hC.σ₁) InputsLt.list_nil))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.emitStepF : (emitStepF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmittedF hC.A₁) (InputsLt.list_cons (InputsLt.isEmittedF hC.A₂)
    (InputsLt.list_cons (InputsLt.isEmitOneF hC.A₃) (InputsLt.list_cons (InputsLt.addConstRel _ hC.A₃.t hC.A₁.t)
    (InputsLt.list_cons (InputsLt.eqFields hC.A₂.t hC.A₃.t) (InputsLt.list_cons (InputsLt.not' hC.σ₁)
    (InputsLt.list_cons hC.σ₂ (InputsLt.list_cons hC.σ₃ InputsLt.list_nil))))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.emitMonoF : (emitMonoF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmittedF hC.A₁) (InputsLt.list_cons (InputsLt.isEmittedF hC.A₂)
    (InputsLt.list_cons (InputsLt.isEmittedF hC.A₃) (InputsLt.list_cons (InputsLt.ltConst _ hC.A₁.t)
    (InputsLt.list_cons (InputsLt.addConstRel _ hC.A₁.t hC.A₂.t) (InputsLt.list_cons (InputsLt.eqFields hC.A₃.t hC.A₂.t)
    (InputsLt.list_cons (InputsLt.not' hC.σ₁) (InputsLt.list_cons hC.σ₂ (InputsLt.list_cons hC.σ₃ InputsLt.list_nil)))))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.emitOneF : (emitOneF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmitOneF hC.A₁) (InputsLt.list_cons (InputsLt.isEmittedF hC.A₂)
    (InputsLt.list_cons (InputsLt.isEmittedF hC.A₃) (InputsLt.list_cons (InputsLt.addConstRel _ hC.A₁.t hC.A₂.t)
    (InputsLt.list_cons (InputsLt.eqFields hC.A₃.t hC.A₂.t) (InputsLt.list_cons (InputsLt.not' hC.σ₁)
    (InputsLt.list_cons hC.σ₂ (InputsLt.list_cons hC.σ₃ InputsLt.list_nil))))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.emitOnceF : (emitOnceF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmitOneF hC.A₁) (InputsLt.list_cons (InputsLt.isEmittedF hC.A₂)
    (InputsLt.list_cons (InputsLt.isEmittedF hC.A₃) (InputsLt.list_cons (InputsLt.eqFields hC.A₂.t hC.A₁.t)
    (InputsLt.list_cons (InputsLt.eqFields hC.A₃.t hC.A₂.t) (InputsLt.list_cons (InputsLt.not' hC.σ₁)
    (InputsLt.list_cons (InputsLt.not' hC.σ₂) (InputsLt.list_cons (InputsLt.not' hC.σ₃) InputsLt.list_nil))))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.emitBadF : (emitBadF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitEmitBadF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.not' hC.σ₁) InputsLt.list_nil)))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.emitPredF : (emitPredF e C).InputsLt n :=
  InputsLt.orList _ (InputsLt.list_cons (InputsLt.emitZeroF e hC) (InputsLt.list_cons (InputsLt.emitStepF e hC)
    (InputsLt.list_cons (InputsLt.emitMonoF e hC) (InputsLt.list_cons (InputsLt.emitOneF e hC)
    (InputsLt.list_cons (InputsLt.emitOnceF e hC) (InputsLt.list_cons (InputsLt.emitBadF e hC) InputsLt.list_nil))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.finalStateF : (finalStateF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitStateF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.t) (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.q)
    (InputsLt.list_cons hC.σ₁ InputsLt.list_nil)))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.finalEmittedF : (finalEmittedF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitEmittedF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.t) (InputsLt.list_cons hC.σ₁ InputsLt.list_nil))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC
theorem InputsLt.finalPredF : (finalPredF e C).InputsLt n :=
  InputsLt.or' (InputsLt.finalStateF e hC) (InputsLt.finalEmittedF e hC)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
theorem InputsLt.mainF {n : ℕ} (tabs : List (ℕ × Fml)) (htabs : ∀ jv ∈ tabs, jv.2.InputsLt n)
    (frees : List ℕ) {C : CandF} (hC : C.InputsLt n) : (mainF e tabs frees C).InputsLt n :=
  InputsLt.orList _ (InputsLt.list_cons (InputsLt.startF e tabs htabs hC) (InputsLt.list_cons (InputsLt.freeF e frees hC)
    (InputsLt.list_cons (InputsLt.bdryPredF e hC) (InputsLt.list_cons (InputsLt.emitPredF e hC)
    (InputsLt.list_cons (InputsLt.finalPredF e hC) InputsLt.list_nil)))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
theorem InputsLt.selectF {n : ℕ} (hot : List Bool) {fs : List Fml} (hfs : ∀ f ∈ fs, f.InputsLt n) :
    (selectF hot fs).InputsLt n := by
  refine InputsLt.orList _ ?_
  intro f hf
  rw [List.mem_iff_getElem] at hf
  obtain ⟨i, hi, rfl⟩ := hf
  rw [List.getElem_zipWith]
  exact InputsLt.and' trivial (hfs _ (List.getElem_mem _))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ}
theorem InputsLt.posF {Fa A : FieldsF} (hFa : Fa.InputsLt n) (hA : A.InputsLt n) (dHot : List Bool)
    (δ : BitStr) : (posF e Fa A dHot δ).InputsLt n := by
  refine InputsLt.selectF _ ?_
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨js, hjs, rfl⟩ := hf
  rw [List.mem_ofFn] at hjs
  obtain ⟨k, rfl⟩ := hjs
  exact InputsLt.addConstRel _ (hFa.js k) hA.p
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ}
theorem InputsLt.winMatchN {Fa A : FieldsF} (hFa : Fa.InputsLt n) (hA : A.InputsLt n) (w : WDesc) :
    (winMatchN e Fa A w).InputsLt n := by
  refine InputsLt.selectF _ ?_
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isCellF hA) (InputsLt.list_cons (InputsLt.eqFields hA.t hFa.t)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.d) (InputsLt.list_cons (InputsLt.posF e hFa hA _ _)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.v) InputsLt.list_nil)))))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isHeadF hA) (InputsLt.list_cons (InputsLt.eqFields hA.t hFa.t)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.d) (InputsLt.list_cons (InputsLt.posF e hFa hA _ _) InputsLt.list_nil))))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isCellF hA) (InputsLt.list_cons (InputsLt.addConstRel _ hFa.t hA.t)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.d) (InputsLt.list_cons (InputsLt.posF e hFa hA _ _)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.v) InputsLt.list_nil)))))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isHeadF hA) (InputsLt.list_cons (InputsLt.addConstRel _ hFa.t hA.t)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.d) (InputsLt.list_cons (InputsLt.posF e hFa hA _ _) InputsLt.list_nil))))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isStateF hA) (InputsLt.list_cons (InputsLt.eqFields hA.t hFa.t)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.q) InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isStateF hA) (InputsLt.list_cons (InputsLt.addConstRel _ hFa.t hA.t)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.q) InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmitOneF hA) (InputsLt.list_cons (InputsLt.eqFields hA.t hFa.t)
      InputsLt.list_nil))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmitBadF hA) (InputsLt.list_cons (InputsLt.eqFields hA.t hFa.t)
      InputsLt.list_nil))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ}
theorem InputsLt.auxMatchN {Fa A : FieldsF} (hFa : Fa.InputsLt n) (hA : A.InputsLt n) (u : BitStr) :
    (auxMatchN e G Fa A u).InputsLt n := by
  refine InputsLt.andList _ ?_
  intro f hf
  rw [List.mem_append, List.mem_ofFn] at hf
  rcases hf with hf | ⟨k, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact InputsLt.isAuxF hA
    · exact InputsLt.eqFields hA.t hFa.t
    · exact InputsLt.eqConst _ hA.g
  · exact InputsLt.eqFields (hA.js k) (hFa.js k)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ}
theorem InputsLt.specMatchN {Fa A : FieldsF} (hFa : Fa.InputsLt n) (hA : A.InputsLt n) (l : LDesc) :
    (specMatchN e G Fa A l).InputsLt n :=
  InputsLt.mux trivial (InputsLt.auxMatchN e G hFa hA _) (InputsLt.winMatchN e hFa hA _)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ}
theorem InputsLt.tplN {C : CandF} (hC : C.InputsLt n) (tp : NTpl) : (tplN e G tp C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.specMatchN e G hC.A₃ hC.A₁ _)
    (InputsLt.list_cons (InputsLt.xnor hC.σ₁ trivial) (InputsLt.list_cons (InputsLt.specMatchN e G hC.A₃ hC.A₂ _)
    (InputsLt.list_cons (InputsLt.xnor hC.σ₂ trivial) (InputsLt.list_cons (InputsLt.specMatchN e G hC.A₃ hC.A₃ _)
    (InputsLt.list_cons (InputsLt.xnor hC.σ₃ trivial) InputsLt.list_nil))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ}
theorem InputsLt.windowGatesN {C : CandF} (hC : C.InputsLt n) (tpls : List (List NTpl)) :
    (windowGatesN e G tpls C).InputsLt n := by
  refine InputsLt.orList _ ?_
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨l, -, rfl⟩ := hf
  refine InputsLt.orList _ ?_
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨tp, -, rfl⟩ := hf
  exact InputsLt.tplN e G hC tp
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ}
theorem InputsLt.windowOutF {C : CandF} (hC : C.InputsLt n) : (windowOutF e G C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitAuxF e G hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.g) (InputsLt.list_cons hC.σ₁ InputsLt.list_nil))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {n : ℕ}
theorem InputsLt.windowN {C : CandF} (hC : C.InputsLt n) (tpls : List (List NTpl)) :
    (windowN e G tpls C).InputsLt n :=
  InputsLt.or' (InputsLt.windowGatesN e G hC tpls) (InputsLt.windowOutF e G hC)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
theorem InputsLt.tableauF {n : ℕ} (tabs : List (ℕ × Fml)) (htabs : ∀ jv ∈ tabs, jv.2.InputsLt n)
    (frees : List ℕ) (tpls : List (List NTpl)) {C : CandF} (hC : C.InputsLt n) :
    (tableauF e G tabs frees tpls C).InputsLt n :=
  InputsLt.or' (InputsLt.mainF e tabs htabs frees hC) (InputsLt.windowN e G hC tpls)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G T : ℕ)
theorem InputsLt.ansEndF {n : ℕ} {C : CandF} (hC : C.InputsLt n) : (ansEndF e T C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC)
    (InputsLt.list_cons (InputsLt.sameSignsF hC) (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁)
    (InputsLt.list_cons (InputsLt.or' (InputsLt.eqConst _ hC.A₁.d) (InputsLt.eqConst _ hC.A₁.d))
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.p) (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.v)
    (InputsLt.list_cons hC.σ₁ InputsLt.list_nil)))))))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G T : ℕ)
theorem InputsLt.tableauPlusF {n : ℕ} (tabs : List (ℕ × Fml)) (htabs : ∀ jv ∈ tabs, jv.2.InputsLt n)
    (frees : List ℕ) (tpls : List (List NTpl)) {C : CandF} (hC : C.InputsLt n) :
    (tableauPlusF e G T tabs frees tpls C).InputsLt n :=
  InputsLt.or' (InputsLt.tableauF e G tabs htabs frees tpls hC) (InputsLt.ansEndF e T hC)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem tabsOf_inputsLt (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) {N : ℕ} {A : FieldsF}
    (hA : A.InputsLt N) : ∀ jv ∈ tabsOf e T D n x y A, jv.2.InputsLt N := by
  intro jv hjv
  simp only [tabsOf, List.mem_cons, List.not_mem_nil, or_false] at hjv
  rcases hjv with rfl | rfl | rfl | rfl | rfl
  · exact InputsLt.cellValF e hA _
  · exact InputsLt.cellValF e hA _
  · exact InputsLt.unaryValF e hA _
  · exact InputsLt.cellValF e hA _
  · exact InputsLt.cellValF e hA _
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
theorem getD_bits (k : ℕ) (i : ℕ) : k.bits.getD i false = k.testBit i := by
  rw [Nat.testBit_eq_inth]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem candOf5_inputsLt (ℓ e T : ℕ) :
    (candOf5 ℓ e T).InputsLt (2 * ℓ + 3 * mOf e Gc + 5) where
  A₁ := litFields_inputsLt e Gc T _ _ (by omega)
  σ₁ := by show 2 * ℓ + 3 * mOf e Gc + 2 < 2 * ℓ + 3 * mOf e Gc + 5; omega
  A₂ := litFields_inputsLt e Gc T _ _ (by omega)
  σ₂ := by show 2 * ℓ + 3 * mOf e Gc + 3 < 2 * ℓ + 3 * mOf e Gc + 5; omega
  A₃ := litFields_inputsLt e Gc T _ _ (by omega)
  σ₃ := by show 2 * ℓ + 3 * mOf e Gc + 4 < 2 * ℓ + 3 * mOf e Gc + 5; omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem descFml5_inputsLt (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr)
    (hℓr : ℓ ≤ mOf e Gc) :
    (descFml5 ℓ T e D n x y).InputsLt (2 * ℓ + 3 * mOf e Gc + 5) :=
  InputsLt.or'
    (InputsLt.tableauPlusF e Gc T _
      (tabsOf_inputsLt e T D n x y (candOf5_inputsLt ℓ e T).A₁) _ _ (candOf5_inputsLt ℓ e T))
    (InputsLt.linkFml ℓ (mOf e Gc) T hℓr)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.SAT
section
open Cost Cost.PolyTimeFun Polynomial
theorem le_ceilPower (n : ℕ) : n ≤ ceilPower n := by
  have h := Nat.lt_size_self (n - 1)
  unfold ceilPower
  omega
end
end MIPRE.SAT

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
/-- The constructed circuit is well formed in the existing circuit interface. -/
theorem circuit_wellFormed {ℓ r m : ℕ} (hℓ : ℓ ≤ m) (hr : r ≤ m)
    (f : Fml) (hf : f.InputsLt (2 * ℓ + 3 * r + 5)) :
    (circuit ℓ r m f).WellFormed :=
  Fml.toCircuit_wellFormed _ (formula_inputsLt hℓ hr f hf)
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
variable {ι : Type*} [SizedEncoding ι]
theorem layoutR_apply (lu ru mu : PolyTimeFun ι Unary) (i : ι) :
    layoutR lu ru mu i = layout (lu i).length (ru i).length (mu i).length := by
  simp [layoutR, baseR_apply, layout]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
variable {ι : Type*} [SizedEncoding ι]
theorem lowR_apply (base : PolyTimeFun ι ℕ) (old mu : PolyTimeFun ι Unary) (i : ι) :
    lowR base old mu i = low (base i) (old i).length (mu i).length := by
  simp only [lowR, ap₂_apply, ltConstP_apply, padToP_apply, fieldP_apply]
  rw [nbitsR_apply (2 ^ (old i).length) (by
    intro j
    simp only [ap₁_apply, pow2P_apply, natBits_apply]
    exact getD_bits _ j)]
  simp [low]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
variable {ι : Type*} [SizedEncoding ι]
theorem formulaR_apply (lu ru mu : PolyTimeFun ι Unary) (f : PolyTimeFun ι Fml) (i : ι) :
    formulaR lu ru mu f i = formula (lu i).length (ru i).length (mu i).length (f i) := by
  simp only [formulaR, orR_apply, andTwo_apply, andR_apply, List.map_cons, List.map_nil,
    lowR_apply, baseR_apply, PolyTimeFun.const_apply, one_mul, ap₂_apply,
    Fml.renameBy_apply, layoutR_apply, notR_apply, blankSignR_apply, ap₁_apply, inc_apply,
    formula]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
variable {ι : Type*} [SizedEncoding ι]
theorem circuitR_apply (lu ru mu : PolyTimeFun ι Unary) (f : PolyTimeFun ι Fml) (i : ι) :
    circuitR lu ru mu f i = circuit (lu i).length (ru i).length (mu i).length (f i) := by
  simp [circuitR, baseR_apply, formulaR_apply, circuit]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
theorem oldWidth_le_innerDim (T σ : ℕ) : mParam T σ ≤ innerDim T σ := le_ceilPower _
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
theorem answerWidth_le_innerDim (T σ : ℕ) : lOf T ≤ innerDim T σ :=
  (lOf_le_mOf T σ).trans (oldWidth_le_innerDim T σ)
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
theorem innerDimU_length (p : DescInput) :
    (innerDimU p).length = innerDim p.1.2.2.1 p.1.2.2.2.2 := by
  simp [innerDimU, innerDim, mParam]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
theorem describe_apply (p : DescInput) : describe p =
    circuit (lOf p.1.2.2.1) (mParam p.1.2.2.1 p.1.2.2.2.2)
      (innerDim p.1.2.2.1 p.1.2.2.2.2)
      (descFml5 (lOf p.1.2.2.1) p.1.2.2.1 (eOf p.1.2.2.1 p.1.2.2.2.2)
        p.1.1 p.1.2.1 p.2.1 p.2.2) := by
  simp only [describe, circuitR_apply, length_dLu, length_mU, length_dEu, innerDimU_length,
    descFml5R_apply, dTR_apply, dDR_apply, dnR_apply, dxR_apply, dyR_apply, mParam]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
theorem describe_wellFormed (p : DescInput) : (describe p).WellFormed := by
  rw [describe_apply]
  apply circuit_wellFormed (answerWidth_le_innerDim _ _) (oldWidth_le_innerDim _ _)
  exact descFml5_inputsLt _ _ _ _ _ _ _ (lOf_le_mOf _ _)
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.SAT.Circuit
section
open Cost Cost.PolyTimeFun
/-- Exact gate padding preserves well-formedness. -/
theorem wellFormed_padGates {C : Circuit} (hC : C.WellFormed) (k : ℕ) :
    (padGates C k).WellFormed := by
  induction k with
  | zero => simpa using hC
  | succ k ih => rw [padGates_succ C hC.nonempty]; exact wellFormed_copyOutput ih
end
end MIPRE.SAT.Circuit

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
theorem describeExact_apply (p : DescInput) (u : Unary) :
    describeExact (p, u) = Circuit.padGates (describe p) (u.length - (describe p).size) := by
  simp [describeExact, Circuit.partsProg, Circuit.size]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
theorem describeExact_wellFormed (p : DescInput) (u : Unary) :
    (describeExact (p, u)).WellFormed := by
  rw [describeExact_apply]
  exact Circuit.wellFormed_padGates (describe_wellFormed p) _
end
end MIPRE.TM.CookLevin.Pad

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Pad
open SAT Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial
set_option maxRecDepth 4096
theorem _root_.solution (D : Prog) (n T Q σ : ℕ) (x y : BitStr) :
    (fixedCircuit D n T Q σ x y).WellFormed := describeExact_wellFormed _ _
end MIPRE.TM.CookLevin.Pad

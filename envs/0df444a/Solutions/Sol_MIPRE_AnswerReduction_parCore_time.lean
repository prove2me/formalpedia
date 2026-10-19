-- Prove2me | solution 1 for MIPRE.AnswerReduction.parCore_time
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:29:46.020086+00:00
-- url     : https://prove2.me/submissions/239c7f38-5eb2-4754-9d74-730bd6343514

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/ParamsCost.lean (solution of MIPRE.AnswerReduction.parCore_time);
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
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Degree.Lemmas
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
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
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
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor
import Definitions.Def_MIPRE_Foundations_OracularComplete
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_OracularTyped
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
import Definitions.Def_MIPRE_Background_LIDT_PresentationQueries
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
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
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Background_AnswerReduction_Layout
import Definitions.Def_MIPRE_Background_AnswerReduction_Family
import Definitions.Def_MIPRE_Background_AnswerReduction_Stages
import Definitions.Def_MIPRE_Background_AnswerReduction_StageLists
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Definitions.Def_MIPRE_Foundations_Introspection_LineRepresentativeProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Introspection_SeededLineProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg
import Definitions.Def_MIPRE_Background_AnswerReduction_StageProg
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_AnswerReduction_StageCorrect
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerProg
import Definitions.Def_MIPRE_Foundations_Cost_FiniteEncoding
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpSampler
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_AnswerReduction
import Definitions.Def_MIPRE_Background_AnswerReduction_Params
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun
import Definitions.Def_MIPRE_Background_AnswerReduction_ParamsCost
import Theorems.Thm_MIPRE_AnswerReduction_ParRoutine_budCore_closed
import Theorems.Thm_MIPRE_AnswerReduction_budCore_time
import Theorems.Thm_MIPRE_AnswerReduction_ctxQT_pdom
import Theorems.Thm_MIPRE_AnswerReduction_params_pdom
import Theorems.Thm_MIPRE_AnswerReduction_post6_apply
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_Cost_seqProg_closed
import Theorems.Thm_MIPRE_Cost_seqProg_runs
import Theorems.Thm_MIPRE_Pipeline_PDom_poly
import Theorems.Thm_MIPRE_Pipeline_PRuns_stage
import Theorems.Thm_MIPRE_Pipeline_stageProg_closed
import Theorems.Thm_MIPRE_Pipeline_toUnaryProg_time

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost
section
open PolyTimeFun
theorem whileProg_closed (f : PolyTimeFun Data (Bool × Data)) : (whileProg f).WellScoped 1 :=
  ⟨Nat.zero_lt_one, f.closed⟩
end
end MIPRE.Cost

namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
theorem toUnaryProg_closed : toUnaryProg.WellScoped 1 :=
  seqProg_closed (PolyTimeFun.closed _) (whileProg_closed _)
end
end MIPRE.Pipeline

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem of_le {c m e v v' : ℕ} (h : PDom W X K c m e v) (hv : v' ≤ v) : PDom W X K c m e v' :=
  hv.trans h
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem mono (hX : 1 ≤ X) {c c' m m' e e' v : ℕ} (h : PDom W X K c m e v) (hc : c ≤ c')
    (hm : m ≤ m') (he : e ≤ e') : PDom W X K c' m' e' v := by
  refine h.trans (Nat.pow_le_pow_left ?_ _)
  exact Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hm))
    (Nat.pow_le_pow_right hX he)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- A base of at least one is below its `(K + 1)`-st power. -/
theorem le_pow_succ {a : ℕ} : a ≤ a ^ (K + 1) :=
  Nat.le_self_pow (by omega) a
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem const (c : ℕ) : PDom W X K (c + 1) 0 0 c := by
  simp only [PDom, pow_zero, Nat.mul_one]
  exact (Nat.le_succ c).trans (le_pow_succ)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- An affine function of `W`. -/
theorem ofAffine {a b v : ℕ} (h : v ≤ a * W + b) : PDom W X K (a + b + 1) 1 0 v := by
  simp only [PDom, pow_one, pow_zero, Nat.mul_one]
  refine h.trans ((?_ : a * W + b ≤ (a + b + 1) * (W + 1)).trans le_pow_succ)
  nlinarith
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- `K + 1 ≤ 2^{K + 1}`: the input sampler's degree itself is dominated. -/
theorem ofLeK {v : ℕ} (h : v ≤ K + 1) : PDom W X K 2 0 0 v := by
  simp only [PDom, pow_zero, Nat.mul_one]
  exact h.trans (Nat.lt_two_pow_self).le
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem add (hX : 1 ≤ X) {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : PDom W X K c₁ m₁ e₁ v₁)
    (h₂ : PDom W X K c₂ m₂ e₂ v₂) :
    PDom W X K (c₁ + c₂) (max m₁ m₂) (max e₁ e₂) (v₁ + v₂) := by
  have h₁' := h₁.mono hX (c' := c₁) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_left _ _)
    (le_max_left _ _)
  have h₂' := h₂.mono hX (c' := c₂) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_right _ _)
    (le_max_right _ _)
  unfold PDom at h₁' h₂' ⊢
  refine (Nat.add_le_add h₁' h₂').trans ?_
  rw [Nat.add_mul, Nat.add_mul]
  exact pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) (by omega)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem mul {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : PDom W X K c₁ m₁ e₁ v₁)
    (h₂ : PDom W X K c₂ m₂ e₂ v₂) : PDom W X K (c₁ * c₂) (m₁ + m₂) (e₁ + e₂) (v₁ * v₂) := by
  unfold PDom at h₁ h₂ ⊢
  refine (Nat.mul_le_mul h₁ h₂).trans (le_of_eq ?_)
  rw [← mul_pow, pow_add, pow_add]
  ring_nf
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- A linear function of `W` and `K + 1`. -/
theorem ofLin (hX : 1 ≤ X) {a b c v : ℕ} (h : v ≤ a * W + b * (K + 1) + c) :
    PDom W X K (a + 2 * b + c + 3) 1 0 v := by
  have h1 : PDom W X K (a + c + 1) 1 0 (a * W + c) := ofAffine le_rfl
  have h2 : PDom W X K ((b + 1) * 2) 0 0 (b * (K + 1)) := (const b).mul (ofLeK le_rfl)
  refine ((h1.add hX h2).mono hX (by nlinarith) (by simp) (by simp)).of_le ?_
  omega
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
theorem esize_nat_le_four (x : ℕ) : esize x ≤ 4 * x + 1 :=
  (esize_nat_le x).trans (by have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := x)); omega)
end
end MIPRE.Pipeline

namespace MIPRE.Pipeline.PRuns
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
variable {W X K : ℕ}
theorem seq (hX : 1 ≤ X) {c₁ m₁ e₁ c₂ m₂ e₂ : ℕ} {p q : Prog} (hq : q.WellScoped 1)
    {x y r : Data} (h₁ : PRuns W X K c₁ m₁ e₁ p x y) (h₂ : PRuns W X K c₂ m₂ e₂ q y r) :
    PRuns W X K (c₁ + c₂ + 2) (max (max m₁ m₂) 0) (max (max e₁ e₂) 0) (seqProg p q) x r :=
  let ⟨_, hs, hp⟩ := h₁
  let ⟨_, ht, hq'⟩ := h₂
  ⟨_, (hs.add hX ht).add hX (PDom.const 1), seqProg_runs hq hp hq'⟩
end
end MIPRE.Pipeline.PRuns

namespace MIPRE.Pipeline.PRuns
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
variable {W X K : ℕ}
/-- **A polynomial-time function's code**, on an input of dominated size. -/
theorem ptf {α β : Type*} [SizedEncoding α] [SizedEncoding β] (f : PolyTimeFun α β)
    (c m e : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (a : α), 1 ≤ X → PDom W X K c m e (esize a) →
      PRuns W X K C M E f.code (encode a) (encode (f a)) :=
  ⟨_, _, _, fun a hX ha => by
    obtain ⟨t, ht, hr⟩ := f.computes a
    exact ⟨t, (ha.poly hX f.timeBound).of_le ht, hr⟩⟩
end
end MIPRE.Pipeline.PRuns

namespace MIPRE.Pipeline.PRuns
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
variable {W X K : ℕ}
/-- **Writing a dominated number in unary.** -/
theorem toUnary (c m e : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (x : ℕ), 1 ≤ X → PDom W X K c m e x →
    PRuns W X K C M E toUnaryProg (encode x) (encode (unary x)) :=
  ⟨_, _, _, fun x hX hx => by
    obtain ⟨t, ht, hr⟩ := toUnaryProg_time x
    refine ⟨t, ?_, hr⟩
    have h4 := ((PDom.const 4).mul hx).add hX (PDom.const 1)
    have h3 := ((PDom.const 4).mul hx).add hX (PDom.const 3)
    exact ((((h4.poly hX toUnaryInit.timeBound).add hX ((hx.add hX (PDom.const 1)).mul
      ((h3.poly hX toUnaryStep.timeBound).add hX (PDom.const 1)))).add hX
      (PDom.const 1))).of_le ht⟩
end
end MIPRE.Pipeline.PRuns

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline SAT StageProg
theorem pdLin {W X K v : ℕ} (hX : 1 ≤ X) (h : v ≤ 40 * W + 40 * (K + 1) + 40) :
    PDom W X K linC 1 0 v :=
  PDom.ofLin hX h
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline SAT StageProg
theorem size_X0 (lam mu sigma n : ℕ) :
    (Data.cons (encode (lam, mu, sigma)) (encode n)).size =
      esize lam + esize mu + esize sigma + esize n + 3 := by
  simp only [Data.size_cons, encode_prod]
  change esize lam + (esize mu + esize sigma + 1) + 1 + esize n + 1 = _
  omega
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline SAT StageProg
open ParRoutine in
theorem _root_.solution (PD : PcpDecider) (R : Polynomial ℕ) : ∃ c m e, ∀ {W X : ℕ},
    ParamsBound PD R → ∀ (lam mu sigma n : ℕ), 1 ≤ X →
    arQ lam mu n ≤ W → lam ≤ W → sigma ≤ W → n ≤ W →
    PRuns W X mu c m e (core PD) (.cons (encode (lam, mu, sigma)) (encode n))
      ((family PD lam mu sigma).pd n) := by
  obtain ⟨cb, mb, eb, hb⟩ := budCore_time
  obtain ⟨cA, mA, eA, hA⟩ := PRuns.stage (ap₂ treePair (PolyTimeFun.id Data)
    (PolyTimeFun.id Data)) postKeep linC 1 0 cb mb eb
  obtain ⟨cx, mx, ex, hx⟩ := ctxQT_pdom
  obtain ⟨cq, mq, eq, hq⟩ := params_pdom PD R
  obtain ⟨cP, mP, eP, hP⟩ := PRuns.ptf (paramsP PD) cx mx ex
  obtain ⟨cu, mu', eu, hu⟩ := PRuns.toUnary cq mq eq
  obtain ⟨c4, m4, e4, h4⟩ := PRuns.stage pre4 postKeep cq mq eq cu mu' eu
  obtain ⟨c5, m5, e5, h5⟩ := PRuns.stage pre5 postKeep cq mq eq cu mu' eu
  obtain ⟨c6, m6, e6, h6⟩ := PRuns.stage pre6 post6 cq mq eq cu mu' eu
  exact ⟨_, _, _, fun {W X} hR lam mu sigma n hX hQ hl hs hn => by
    set P := arPar PD lam mu sigma n with hPdef
    have hq' := hq (W := W) hR lam mu sigma n hX hQ hs hn
    rw [← hPdef] at hq'
    have el := esize_nat_le_four lam
    have em := esize_nat_le_four mu
    have es := esize_nat_le_four sigma
    have en := esize_nat_le_four n
    let X0 : Data := .cons (encode (lam, mu, sigma)) (encode n)
    have hX0 : X0.size = esize lam + esize mu + esize sigma + esize n + 3 := size_X0 _ _ _ _
    have SA := hA (W := W) (K := mu) budCore_closed X0 X0 X0 _ hX (by simp)
      (pdLin hX (by omega)) (hb (W := W) lam mu sigma n hX hQ hl hs hn)
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at SA
    let X1 : Data := .cons (encode (arQ lam mu n, tPcp lam mu n)) X0
    have SP := hP (W := W) (K := mu) X1 hX (hx lam mu sigma n hX hQ hl hs hn)
    have hp : paramsP PD X1 = encode (P.k, P.m, P.s) := by
      simp only [paramsP, comp_apply, pair_apply, treeHead_cons, treeTail_cons, readNat_encode,
        encoded_apply, X1, X0, encode_prod, PD.paramsProg_eq]
      rfl
    rw [encode_data, hp, encode_data] at SP
    have ek := esize_nat_le_four P.k
    have emm := esize_nat_le_four P.m
    have ess := esize_nat_le_four P.s
    let X3 : Data := encode (P.k, P.m, P.s)
    have hX3 : X3.size = esize P.k + esize P.m + esize P.s + 2 := by
      simp only [X3, encode_prod, Data.size_cons]
      change esize P.k + (esize P.m + esize P.s + 1) + 1 = _
      omega
    have S4 := h4 (W := W) (K := mu) toUnaryProg_closed X3 (encode P.k) X3 _ hX rfl
      (hq'.of_le (by omega)) (hu (W := W) (K := mu) P.k hX (hq'.of_le (by omega)))
    let X4 : Data := .cons (encode (unary P.k)) X3
    have hX4 : X4.size = 2 * P.k + 1 + X3.size + 1 := by
      simp only [X4, Data.size_cons]
      rw [show (encode (unary P.k) : Data).size = esize (unary P.k) from rfl, esize_unary]
    have S5 := h5 (W := W) (K := mu) toUnaryProg_closed X4 (encode P.m) X4 _ hX rfl
      (hq'.of_le (by omega)) (hu (W := W) (K := mu) P.m hX (hq'.of_le (by omega)))
    let X5 : Data := .cons (encode (unary P.m)) X4
    have hX5 : X5.size = 2 * P.m + 1 + X4.size + 1 := by
      simp only [X5, Data.size_cons]
      rw [show (encode (unary P.m) : Data).size = esize (unary P.m) from rfl, esize_unary]
    have S6 := h6 (W := W) (K := mu) toUnaryProg_closed X5 (encode P.s) X5 _ hX rfl
      (hq'.of_le (by omega)) (hu (W := W) (K := mu) P.s hX (hq'.of_le (by omega)))
    rw [post6_apply] at S6
    exact PRuns.seq hX (seqProg_closed (PolyTimeFun.closed _) <|
        seqProg_closed (stageProg_closed _ toUnaryProg_closed _) <|
        seqProg_closed (stageProg_closed _ toUnaryProg_closed _)
          (stageProg_closed _ toUnaryProg_closed _)) SA <|
      PRuns.seq hX (seqProg_closed (stageProg_closed _ toUnaryProg_closed _) <|
        seqProg_closed (stageProg_closed _ toUnaryProg_closed _)
          (stageProg_closed _ toUnaryProg_closed _)) SP <|
      PRuns.seq hX (seqProg_closed (stageProg_closed _ toUnaryProg_closed _)
          (stageProg_closed _ toUnaryProg_closed _)) S4 <|
      PRuns.seq hX (stageProg_closed _ toUnaryProg_closed _) S5 S6⟩
end MIPRE.AnswerReduction

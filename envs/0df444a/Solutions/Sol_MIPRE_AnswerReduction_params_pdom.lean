-- Prove2me | solution 1 for MIPRE.AnswerReduction.params_pdom
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:22:15.604648+00:00
-- url     : https://prove2.me/submissions/4f511e28-f753-451e-bbe2-ac7a80c5e346

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/ParamsCost.lean (solution of MIPRE.AnswerReduction.params_pdom);
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
import Theorems.Thm_MIPRE_Pipeline_PDom_poly

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
/-- The argument of the parameter bound, `|n| + |T| + Q + σ`. -/
theorem size_tPcp (lam mu n : ℕ) :
    Nat.size (tPcp lam mu n) = (arQ lam mu n + 5) * (mu + 1) + 1 := by
  rw [tPcp, Nat.size_pow]
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline SAT StageProg
theorem _root_.solution (PD : PcpDecider) (R : Polynomial ℕ) : ∃ c m e, ∀ {W X : ℕ},
    ParamsBound PD R → ∀ (lam mu sigma n : ℕ), 1 ≤ X → arQ lam mu n ≤ W → sigma ≤ W → n ≤ W →
    PDom W X mu c m e (20 * ((arPar PD lam mu sigma n).k + (arPar PD lam mu sigma n).m +
      (arPar PD lam mu sigma n).s) + 20) := by
  exact ⟨_, _, _, fun {W X} hR lam mu sigma n hX hQ hs hn => by
    have hsn : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    have h1 : PDom W X mu _ _ _ (Nat.size n + arQ lam mu n + sigma + 1) := pdLin hX (by omega)
    have h2 : PDom W X mu _ _ _ ((arQ lam mu n + 5) * (mu + 1)) :=
      (pdLin hX (by omega : arQ lam mu n + 5 ≤ 40 * W + 40 * (mu + 1) + 40)).mul
        (pdLin hX (by omega : mu + 1 ≤ 40 * W + 40 * (mu + 1) + 40))
    have h3 := (h1.add hX h2).poly hX R
    have hk := hR n (tPcp lam mu n) (arQ lam mu n) sigma
    rw [size_tPcp] at hk
    have h4 : R.eval (Nat.size n + ((arQ lam mu n + 5) * (mu + 1) + 1) + arQ lam mu n + sigma) ≤
        R.eval (Nat.size n + arQ lam mu n + sigma + 1 + (arQ lam mu n + 5) * (mu + 1)) :=
      polynomial_eval_mono _ (by omega)
    exact (((PDom.const 20).mul (h3.of_le (hk.trans h4))).add hX (PDom.const 20)).of_le
      (by simp only [arPar]; omega)⟩
end MIPRE.AnswerReduction

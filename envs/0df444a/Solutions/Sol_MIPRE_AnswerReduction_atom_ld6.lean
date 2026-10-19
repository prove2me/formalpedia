-- Prove2me | solution 1 for MIPRE.AnswerReduction.atom_ld6
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:25:08.297107+00:00
-- url     : https://prove2.me/submissions/00b84d6b-26fd-4dda-9c46-947fb9668219

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/DecideSpec.lean (solution of MIPRE.AnswerReduction.atom_ld6);
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
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Definitions.Def_MIPRE_Background_AnswerReduction_Predicate
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
import Definitions.Def_MIPRE_Background_AnswerReduction_AnswerFormat
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
import Definitions.Def_MIPRE_Background_AnswerReduction_TypedGame
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
import Definitions.Def_MIPRE_Foundations_Introspection_FieldPolynomialProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldLineCheckProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldQuestionProg
import Definitions.Def_MIPRE_Background_AnswerReduction_DecideSpec
import Theorems.Thm_MIPRE_AnswerReduction_Pcp_regs6_eq
import Theorems.Thm_MIPRE_AnswerReduction_StageProg_ptMapL_vecBits
import Theorems.Thm_MIPRE_AnswerReduction_ldB_aline
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_Introspection_FieldLineCheck_parameter_eq
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits
import Theorems.Thm_MIPRE_SAT_shoupBinField_charP
import Theorems.Thm_MIPRE_SAT_shoupInvProg_correct
import Theorems.Thm_MIPRE_SAT_shoupMulProg_encoding

attribute [instance] MIPRE.SAT.shoupBinField_charP

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT
section
open Cost
theorem bitsVal_cons' (b : Bool) (l : BitStr) : bitsVal (b :: l) = 2 * bitsVal l + b.toNat := by
  rw [bitsVal_cons]; cases b <;> simp [Nat.bit]
end
end MIPRE.SAT

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_2
theorem vectorBits_injective {k : ℕ} : Function.Injective (vectorBits (n := k)) := by
  intro v w h
  have he := congrArg (vectorValue k) h
  simpa using he
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryPolynomial LowDegree.BinaryLinear
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_1
/-- Canonical field encodings and canonical linear coordinates coincide exactly. -/
theorem shoupCoordinateEquiv_encoding (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) :
    vectorBits (shoupCoordinateEquiv k hk a) = (shoupBinField k hk).toBits a :=
  vectorBits_vectorValue k _ ((shoupBinField k hk).length_toBits a)
end
end MIPRE.SAT

namespace MIPRE.AnswerReduction.Pcp
section
variable {α : Type*}
variable {F : Type*} [Zero F]
omit [Zero F] in
/-- **Slicing a vector** is slicing its list of entries. -/
theorem ofFn_sliceV (g : F → α) {N : ℕ} (o sz : ℕ) (h : o + sz ≤ N) (v : Fin N → F) :
    List.ofFn (fun j => g (sliceV o sz h v j)) = sliceL o sz (List.ofFn fun r => g (v r)) := by
  apply List.ext_getElem
  · simp [sliceL]; omega
  · intro i h1 h2
    simp [sliceL, sliceV]
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.Introspection.SeedProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem bitsVal_drop (l : BitStr) (n : ℕ) :
    bitsVal (l.drop n) = bitsVal l / 2 ^ n := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    cases l with
    | nil => simp
    | cons b l =>
      rw [List.drop_succ_cons, ih, SAT.bitsVal_cons', pow_succ,
        Nat.mul_comm (2 ^ n) 2, ← Nat.div_div_eq_div_mul]
      have h : (2 * bitsVal l + b.toNat) / 2 = bitsVal l := by
        cases b
        · simp
        · simp only [Bool.toNat_true]; omega
      rw [h]
end
end MIPRE.Introspection.SeedProgram

namespace MIPRE.Introspection.SeedProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
/-- The exact connection between the equal-block selector and its bit scan. -/
theorem selector_eq_bits {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (a : E.carrier) :
    (selector E j hj a).val = bitsVal ((E.toBits a).drop (k - j)) := by
  rw [bitsVal_drop]
  rfl
end
end MIPRE.Introspection.SeedProgram

namespace MIPRE.Introspection.SeedProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem selectorProg_apply (k j : Unary) (s : BitStr) :
    selectorProg (k, j, s) = bitsVal (s.drop (k.length - j.length)) := by
  change bitsVal (s.drop (k.drop j.length).length) = _
  rw [List.length_drop]
end
end MIPRE.Introspection.SeedProgram

namespace MIPRE.Introspection.SeedProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem selectorProg_correct {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (a : E.carrier) :
    selectorProg (unary k, unary j, E.toBits a) = (selector E j hj a).val := by
  rw [selectorProg_apply, length_unary, length_unary, selector_eq_bits]
end
end MIPRE.Introspection.SeedProgram

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
local instance instFactPrimeOfNatNat_mIPRE_6 : Fact (Nat.Prime 2) := ⟨by decide⟩
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupZeroProg_correct (k : ℕ) (hk : 1 ≤ k) :
    shoupZeroProg (unary k) = (shoupBinField k hk).toBits 0 := by
  rw [← shoupCoordinateEquiv_encoding, map_zero]
  change (unary k).map (fun _ => false) = vectorBits (0 : Fin k → ZMod 2)
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    simp [vectorBits, bit]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupNonzeroRow_correct (k : ℕ) (hk : 1 ≤ k) (a : (shoupBinField k hk).carrier) :
    nonzeroRow ((shoupBinField k hk).toBits a) = decide (a ≠ 0) := by
  rw [← shoupCoordinateEquiv_encoding]
  unfold nonzeroRow
  rw [zeroRow_vectorBits, ← (shoupCoordinateEquiv k hk).map_zero]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact not_congr ((vectorBits_injective (k := k)).eq_iff.trans
    (shoupCoordinateEquiv k hk).injective.eq_iff)
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupXorBits_correct (k : ℕ) (hk : 1 ≤ k) (a b : (shoupBinField k hk).carrier) :
    BinaryPolynomial.xorBits ((shoupBinField k hk).toBits a) ((shoupBinField k hk).toBits b) =
      (shoupBinField k hk).toBits (a + b) := by
  simp only [← shoupCoordinateEquiv_encoding, xorBits_vectorBits, map_add]
end
end MIPRE.SAT

namespace MIPRE.Introspection.LineProgram
noncomputable section
open Cost Cost.PolyTimeFun Polynomial LowDegree LowDegree.BinaryLinear SAT
theorem firstPairBitsProg_correct (k : ℕ) (hk : 1 ≤ k)
    (l : List ((shoupBinField k hk).carrier × (shoupBinField k hk).carrier)) :
    firstPairBitsProg
      (l.map (fun p => ((shoupBinField k hk).toBits p.1, (shoupBinField k hk).toBits p.2)),
        ((shoupBinField k hk).toBits 0, (shoupBinField k hk).toBits 0)) =
      ((shoupBinField k hk).toBits (firstPair l).1,
        (shoupBinField k hk).toBits (firstPair l).2) := by
  change (l.map _).foldr _ _ = _
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.foldr_cons, shoupNonzeroRow_correct, ih]
    by_cases ha : a.2 = 0 <;> simp [firstPair, ha]
end
end MIPRE.Introspection.LineProgram

namespace MIPRE.Introspection.LineProgram
noncomputable section
open Cost Cost.PolyTimeFun Polynomial LowDegree LowDegree.BinaryLinear SAT
theorem coefficientOfPairProg_correct (k : ℕ) (hk : 1 ≤ k)
    (a c : (shoupBinField k hk).carrier) :
    coefficientOfPairProg (unary k, (shoupBinField k hk).toBits a,
      (shoupBinField k hk).toBits c) =
      (shoupBinField k hk).toBits (if c ≠ 0 then a * c⁻¹ else 0) := by
  change (if nonzeroRow ((shoupBinField k hk).toBits c) then
    shoupMulProg (unary k, (shoupBinField k hk).toBits a,
      shoupInvProg (unary k, (shoupBinField k hk).toBits c)) else
    shoupZeroProg (unary k)) = _
  rw [shoupNonzeroRow_correct]
  by_cases hc : c = 0
  · simp only [hc, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
    exact shoupZeroProg_correct k hk
  · simp only [hc, ne_eq, not_false_eq_true, decide_true, if_true]
    rw [shoupInvProg_correct k hk c hc, shoupMulProg_encoding]
end
end MIPRE.Introspection.LineProgram

namespace MIPRE.Introspection.LineProgram
noncomputable section
open Cost Cost.PolyTimeFun Polynomial LowDegree LowDegree.BinaryLinear SAT
theorem coefficientBitsProg_correct (k : ℕ) (hk : 1 ≤ k)
    (l : List ((shoupBinField k hk).carrier × (shoupBinField k hk).carrier)) :
    coefficientBitsProg
      (unary k, l.map (fun p => ((shoupBinField k hk).toBits p.1,
        (shoupBinField k hk).toBits p.2))) =
      (shoupBinField k hk).toBits (coefficient l) := by
  change coefficientOfPairProg (unary k, firstPairBitsProg
    (l.map _, (shoupZeroProg (unary k), shoupZeroProg (unary k)))) = _
  rw [shoupZeroProg_correct k hk, firstPairBitsProg_correct,
    coefficientOfPairProg_correct]
  rfl
end
end MIPRE.Introspection.LineProgram

namespace MIPRE.Introspection.SeededLineProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT SeedProgram LineProgram
theorem maskBeforeProg_apply (k : Unary) (i : ℕ) (v : List BitStr) :
    maskBeforeProg (k, i, v) = ((List.range' 0 v.length).zip v).map
      (fun p => if i ≤ p.1 then p.2 else shoupZeroProg k) := by
  simp [maskBeforeProg, maskBeforeStep, indexedRows_apply]
end
end MIPRE.Introspection.SeededLineProgram

namespace MIPRE.Introspection.SeededLineProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT SeedProgram LineProgram
theorem maskBeforeProg_correct (k : ℕ) (hk : 1 ≤ k) {n : ℕ} (i : ℕ)
    (v : Fin n → (shoupBinField k hk).carrier) :
    maskBeforeProg (unary k, i, (shoupBinField k hk).vecBits v) =
      (shoupBinField k hk).vecBits (fun j => if j.val < i then 0 else v j) := by
  rw [maskBeforeProg_apply, shoupZeroProg_correct k hk]
  apply List.ext_getElem
  · simp [BinField.vecBits]
  · intro j hj hj'
    simp only [BinField.vecBits, List.length_map, List.length_ofFn,
      List.getElem_map, List.getElem_zip, List.getElem_range', zero_add,
      List.getElem_ofFn]
    by_cases h : i ≤ j
    · simp [h, Nat.not_lt.mpr h]
    · simp [h, Nat.lt_of_not_ge h]
end
end MIPRE.Introspection.SeededLineProgram

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
theorem vecBits_eq_ofFn {N : ℕ} (v : Fin N → ((shoupBinField k hk)).carrier) :
    ((shoupBinField k hk)).vecBits v = List.ofFn fun r => ((shoupBinField k hk)).toBits (v r) := by
  simp [BinField.vecBits, List.map_ofFn]
  rfl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
theorem vecBits_sliceV {N : ℕ} (o sz : ℕ) (h : o + sz ≤ N) (v : Fin N → ((shoupBinField k hk)).carrier) :
    ((shoupBinField k hk)).vecBits (sliceV o sz h v) = sliceL o sz (((shoupBinField k hk)).vecBits v) := by
  rw [vecBits_eq_ofFn, vecBits_eq_ofFn]
  exact ofFn_sliceV ((shoupBinField k hk)).toBits o sz h v
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (o sz jw : ℕ) (c : Fin 6)
theorem seedOf_vecBits (s6 : Fin 6 → ((shoupBinField k hk)).carrier) :
    seedOf (unary o, unary sz, unary jw, unary c) (((shoupBinField k hk)).vecBits s6) = ((shoupBinField k hk)).toBits (s6 c) := by
  rw [seedOf, length_unary, vecBits_eq_ofFn, List.drop_eq_getElem_cons (by simp),
    List.headD_cons, List.getElem_ofFn]
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (o sz jw : ℕ) (c : Fin 6)
variable [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz) (hjw : jw ≤ k)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
include hjw hχ in
theorem selDirL_vecBits (s : ((shoupBinField k hk)).carrier) (w : Fin sz → ((shoupBinField k hk)).carrier) :
    selDirL (unary k) (unary o, unary sz, unary jw, unary c) (((shoupBinField k hk)).toBits s) (((shoupBinField k hk)).vecBits w) =
      ((shoupBinField k hk)).vecBits (zeroBelow (S.χ s) w) := by
  change maskBeforeProg (unary k, selectorProg (unary k, unary jw, ((shoupBinField k hk)).toBits s),
    ((shoupBinField k hk)).vecBits w) = _
  rw [selectorProg_correct _ jw hjw, ← hχ, maskBeforeProg_correct k hk]
  rfl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.Introspection.FieldPolynomialProgram
noncomputable section
open Cost Cost.PolyTimeFun Polynomial LowDegree.BinaryPolynomial SAT
/-- This is the coefficient-vector evaluation used by the line-test semantics. -/
theorem evalCoeffs_ofFn {R : Type*} [CommSemiring R] (x : R) {n : ℕ}
    (f : Fin n → R) : evalCoeffs x (List.ofFn f) = ∑ i, f i * x ^ (i : ℕ) := by
  induction n with
  | zero => simp [evalCoeffs]
  | succ n ih =>
    rw [List.ofFn_succ, evalCoeffs_cons, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ,
      Finset.sum_mul, mul_assoc]
    exact add_comm _ _
end
end MIPRE.Introspection.FieldPolynomialProgram

namespace MIPRE.Introspection.FieldPolynomialProgram
noncomputable section
open Cost Cost.PolyTimeFun Polynomial LowDegree.BinaryPolynomial SAT
theorem shoupHornerProg_correct (k : ℕ) (hk : 1 ≤ k)
    (x : (shoupBinField k hk).carrier) (coeffs : List (shoupBinField k hk).carrier) :
    shoupHornerProg (unary k, (shoupBinField k hk).toBits x,
      coeffs.map (shoupBinField k hk).toBits) =
      (shoupBinField k hk).toBits (evalCoeffs x coeffs) := by
  change (coeffs.map (shoupBinField k hk).toBits).foldr
    (fun c a => xorBits (mulReduce (shoupLowerCoeffs (unary k)) a
      ((shoupBinField k hk).toBits x)) c) (shoupZeroProg (unary k)) = _
  rw [shoupZeroProg_correct k hk]
  induction coeffs with
  | nil => rfl
  | cons c coeffs ih =>
    rw [List.map_cons, List.foldr_cons, ih]
    change xorBits (shoupMulProg (unary k,
      (shoupBinField k hk).toBits (evalCoeffs x coeffs),
      (shoupBinField k hk).toBits x)) ((shoupBinField k hk).toBits c) = _
    rw [shoupMulProg_encoding, shoupXorBits_correct]
    rfl
end
end MIPRE.Introspection.FieldPolynomialProgram

namespace MIPRE.Introspection.FieldPolynomialProgram
noncomputable section
open Cost Cost.PolyTimeFun Polynomial LowDegree.BinaryPolynomial SAT
/-- Canonical fixed-length vectors evaluate to the expected power sum. -/
theorem shoupHornerProg_ofFn (k : ℕ) (hk : 1 ≤ k) {n : ℕ}
    (x : (shoupBinField k hk).carrier) (f : Fin n → (shoupBinField k hk).carrier) :
    shoupHornerProg (unary k, (shoupBinField k hk).toBits x,
      (shoupBinField k hk).vecBits f) =
      (shoupBinField k hk).toBits (∑ i, f i * x ^ (i : ℕ)) := by
  rw [← evalCoeffs_ofFn]
  simpa only [BinField.vecBits, List.map_ofFn] using shoupHornerProg_correct k hk x (List.ofFn f)
end
end MIPRE.Introspection.FieldPolynomialProgram

namespace MIPRE.Introspection.FieldLineCheck
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryPolynomial LineProgram FieldPolynomialProgram CL.Detyping.Program
theorem membership_iff {F : Type*} [Field F] [DecidableEq F] {m : ℕ}
    (origin direction point : Fin m → F) :
    point = origin + parameter origin direction point • direction ↔
      ∃ t : F, point = origin + t • direction := by
  constructor
  · exact fun h => ⟨_, h⟩
  · rintro ⟨t, ht⟩
    by_cases hd : ∃ j, direction j ≠ 0
    · have hp : parameter origin direction point = t := by
        rw [parameter_eq, dif_pos hd, ht]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
        exact mul_div_cancel_right₀ t (Fin.find_spec hd)
      rw [hp]
      exact ht
    · have hz : direction = 0 := by ext i; simpa using (not_exists.mp hd i)
      simpa [hz] using ht
end
end MIPRE.Introspection.FieldLineCheck

namespace MIPRE.Introspection.FieldLineCheck
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryPolynomial LineProgram FieldPolynomialProgram CL.Detyping.Program
theorem subtractProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x y : Fin m → (shoupBinField k hk).carrier) :
    subtractProg ((shoupBinField k hk).vecBits x, (shoupBinField k hk).vecBits y) =
      (shoupBinField k hk).vecBits (x - y) := by
  have hz : ((shoupBinField k hk).vecBits x).zip ((shoupBinField k hk).vecBits y) =
      List.ofFn (fun i => ((shoupBinField k hk).toBits (x i),
        (shoupBinField k hk).toBits (y i))) := by
    apply List.ext_getElem <;> simp [BinField.vecBits]
  change List.map xorBitsProg _ = _
  rw [zip_apply, hz]
  simp only [List.map_ofFn, Function.comp_def, xorBitsProg_apply,
    shoupXorBits_correct, BinField.vecBits, Pi.sub_apply, CharTwo.sub_eq_add]
end
end MIPRE.Introspection.FieldLineCheck

namespace MIPRE.Introspection.FieldLineCheck
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryPolynomial LineProgram FieldPolynomialProgram CL.Detyping.Program
theorem parameterProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (origin direction point : Fin m → (shoupBinField k hk).carrier) :
    parameterProg (unary k, (shoupBinField k hk).vecBits origin,
      (shoupBinField k hk).vecBits direction, (shoupBinField k hk).vecBits point) =
      (shoupBinField k hk).toBits (parameter origin direction point) := by
  have hz : ((shoupBinField k hk).vecBits (point - origin)).zip
      ((shoupBinField k hk).vecBits direction) =
      (List.ofFn (fun i => (point i - origin i, direction i))).map
        (fun p => ((shoupBinField k hk).toBits p.1, (shoupBinField k hk).toBits p.2)) := by
    apply List.ext_getElem <;> simp [BinField.vecBits]
  simp only [parameterProg, comp_apply, pair_apply, fst_apply, snd_apply,
    subtractProg_correct, zip_apply, hz, coefficientBitsProg_correct, parameter]
end
end MIPRE.Introspection.FieldLineCheck

namespace MIPRE.Introspection.FieldLineCheck
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryPolynomial LineProgram FieldPolynomialProgram CL.Detyping.Program
theorem affineProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (t : (shoupBinField k hk).carrier)
    (origin direction : Fin m → (shoupBinField k hk).carrier) :
    affineProg (unary k, (shoupBinField k hk).toBits t,
      (shoupBinField k hk).vecBits origin, (shoupBinField k hk).vecBits direction) =
      (shoupBinField k hk).vecBits (origin + t • direction) := by
  have hz : ((shoupBinField k hk).vecBits origin).zip ((shoupBinField k hk).vecBits direction) =
      List.ofFn (fun i => ((shoupBinField k hk).toBits (origin i),
        (shoupBinField k hk).toBits (direction i))) := by
    apply List.ext_getElem <;> simp [BinField.vecBits]
  simp only [affineProg, comp_apply, pair_apply, fst_apply, snd_apply,
    zip_apply, hz, mapWith_apply, List.map_ofFn, Function.comp_def]
  simp only [BinField.vecBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change xorBits ((shoupBinField k hk).toBits (origin i))
    (shoupMulProg (unary k, (shoupBinField k hk).toBits t,
      (shoupBinField k hk).toBits (direction i))) = _
  rw [shoupMulProg_encoding, shoupXorBits_correct]
  rfl
end
end MIPRE.Introspection.FieldLineCheck

namespace MIPRE.Introspection.FieldLineCheck
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryPolynomial LineProgram FieldPolynomialProgram CL.Detyping.Program
theorem memberProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (origin direction point : Fin m → (shoupBinField k hk).carrier) :
    memberProg (unary k, (shoupBinField k hk).vecBits origin,
      (shoupBinField k hk).vecBits direction, (shoupBinField k hk).vecBits point) = true ↔
      ∃ t : (shoupBinField k hk).carrier, point = origin + t • direction := by
  simp only [memberProg, comp_apply, pair_apply, fst_apply, snd_apply,
    parameterProg_correct, affineProg_correct, encoded_apply, treeEq_apply,
    decide_eq_true_eq, encode_injective.eq_iff, (vecBits_injective (shoupBinField k hk)).eq_iff,
    membership_iff]
end
end MIPRE.Introspection.FieldLineCheck

namespace MIPRE.Introspection.FieldLineCheck
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryPolynomial LineProgram FieldPolynomialProgram CL.Detyping.Program
theorem lineCheckProg_correct (k : ℕ) (hk : 1 ≤ k) {m n : ℕ}
    (origin direction point : Fin m → (shoupBinField k hk).carrier)
    (f : Fin n → (shoupBinField k hk).carrier) (a : (shoupBinField k hk).carrier) :
    lineCheckProg ((unary k, (shoupBinField k hk).vecBits origin,
      (shoupBinField k hk).vecBits direction, (shoupBinField k hk).vecBits point),
      (shoupBinField k hk).vecBits f, (shoupBinField k hk).toBits a) = true ↔
      (∃ t : (shoupBinField k hk).carrier, point = origin + t • direction) ∧
        (∑ i, f i * parameter origin direction point ^ (i : ℕ)) = a := by
  have hi : Function.Injective (shoupBinField k hk).toBits := by
    intro x y h
    simpa only [(shoupBinField k hk).ofBits_toBits] using congrArg (shoupBinField k hk).ofBits h
  simp only [lineCheckProg, PolyTimeFun.ite_apply, comp_apply, pair_apply, fst_apply, snd_apply,
    parameterProg_correct, shoupHornerProg_ofFn, ArrayProg.eqBits_apply,
    const_apply, Bool.ite_eq_true_distrib, Bool.false_eq_true,
    decide_eq_true_eq, hi.eq_iff, memberProg_correct]
  split <;> simp_all
end
end MIPRE.Introspection.FieldLineCheck

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
theorem chunks_eq {α : Type*} (w : ℕ) : ∀ (n : ℕ) (l : List α),
    chunks w n l = List.ofFn fun c : Fin n => (l.drop (c * w)).take w
  | 0, _ => rfl
  | n + 1, l => by
    rw [chunks, chunks_eq w n, List.ofFn_succ]
    congr 1
    · simp
    · congr 1
      funext c
      simp only [Fin.val_succ, List.drop_drop, Nat.succ_mul]
      rw [Nat.add_comm w]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
theorem chunks_ofFn {α : Type*} (w n : ℕ) (g : Fin n → Fin w → α) :
    chunks w n (List.ofFn fun r : Fin (n * w) => g (finProdFinEquiv.symm r).1
      (finProdFinEquiv.symm r).2) = List.ofFn fun c => List.ofFn (g c) := by
  rw [chunks_eq]
  apply congrArg List.ofFn
  funext c
  have hc : (c : ℕ) * w + w ≤ n * w := by
    have := c.isLt
    nlinarith
  apply List.ext_getElem
  · simp; omega
  · intro j h₁ h₂
    simp only [List.length_ofFn] at h₂
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    have hw : 0 < w := by omega
    congr 1
    · apply Fin.ext
      simp only [finProdFinEquiv_symm_apply, Fin.coe_divNat]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt h₂, zero_add]
    · apply Fin.ext
      simp only [finProdFinEquiv_symm_apply, Fin.coe_modNat]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₂]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k)
theorem lineParam_eq {m : ℕ} (u₀ w x : Point ((shoupBinField k hk)).carrier m) :
    lineParam u₀ w x = parameter u₀ w x := by
  rw [parameter_eq]; rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k)
theorem lvpB_eq {m ldc d : ℕ} [NeZero ldc] (u₀ w x : Point ((shoupBinField k hk)).carrier m)
    (f : Fin ldc → LinePoly ((shoupBinField k hk)).carrier d) (a : Fin ldc → ((shoupBinField k hk)).carrier) :
    lvpB (unary k) (((shoupBinField k hk)).vecBits u₀) (((shoupBinField k hk)).vecBits w) (((shoupBinField k hk)).vecBits x)
      (List.ofFn fun j => ((shoupBinField k hk)).vecBits (f j)) (((shoupBinField k hk)).vecBits a) = lineVsPoint u₀ w x f a := by
  have hz : (List.ofFn fun j => ((shoupBinField k hk)).vecBits (f j)).zip (((shoupBinField k hk)).vecBits a) =
      List.ofFn fun j => (((shoupBinField k hk)).vecBits (f j), ((shoupBinField k hk)).toBits (a j)) := by
    apply List.ext_getElem <;> simp [BinField.vecBits]
  rw [lvpB, hz, lineVsPoint]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    lineCheckProg_correct k hk, decide_eq_true_eq, LinePoly.eval, lineParam_eq]
  constructor
  · intro h
    exact ⟨(h 0).1, fun j => (h j).2⟩
  · rintro ⟨h₁, h₂⟩ j
    exact ⟨h₁, h₂ j⟩
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (P : PcpParams)
variable (o sz jw : ℕ) (c : Fin 6) (h : o + sz ≤ P.m') (hjw : jw ≤ k) (hsz2 : sz = 2 ^ jw)
  [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
omit [NeZero sz] in
theorem seedOf_blocksV (y : Coord P → ((shoupBinField k hk)).carrier) :
    seedOf (((unary o, unary sz, unary jw, unary c) : Desc)) (blocksV hk P y).2.2 = ((shoupBinField k hk)).toBits (y ((regsAt P o sz c h)).coord) :=
  seedOf_vecBits hk o sz jw c _
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (P : PcpParams)
variable (o sz jw : ℕ) (c : Fin 6) (h : o + sz ≤ P.m') (hjw : jw ≤ k) (hsz2 : sz = 2 ^ jw)
  [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
omit [NeZero sz] in
theorem pt_blocksV (y : Coord P → ((shoupBinField k hk)).carrier) :
    sliceL (unary o).length (unary sz).length (blocksV hk P y).1 = ((shoupBinField k hk)).vecBits (((regsAt P o sz c h)).ptOf y) := by
  rw [length_unary, length_unary, blocksV, ← vecBits_sliceV hk o sz h]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (P : PcpParams)
variable (o sz jw : ℕ) (c : Fin 6) (h : o + sz ≤ P.m') (hjw : jw ≤ k) (hsz2 : sz = 2 ^ jw)
  [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
omit [NeZero sz] in
theorem dir_blocksV (y : Coord P → ((shoupBinField k hk)).carrier) :
    sliceL (unary o).length (unary sz).length (blocksV hk P y).2.1 =
      ((shoupBinField k hk)).vecBits (((regsAt P o sz c h)).dirOf y) := by
  rw [length_unary, length_unary, blocksV, ← vecBits_sliceV hk o sz h]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (P : PcpParams)
variable (o sz jw : ℕ) (c : Fin 6) (h : o + sz ≤ P.m') (hjw : jw ≤ k) (hsz2 : sz = 2 ^ jw)
  [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
include hχ in
/-- **The diagonal subtest**. -/
theorem ldB_dline {ldc d : ℕ} [NeZero ldc] (xp xq : Coord P → ((shoupBinField k hk)).carrier)
    (av : Fin ldc → ((shoupBinField k hk)).carrier) (f : Fin ldc → LinePoly ((shoupBinField k hk)).carrier (sz * d)) :
    ldB (unary k) (((unary o, unary sz, unary jw, unary c) : Desc)) 2 (blocksV hk P xp) (blocksV hk P xq) (List.ofFn fun j => ((shoupBinField k hk)).vecBits (f j))
      (((shoupBinField k hk)).vecBits av) =
    LIDT.CL.accepts hsz ((((regsAt P o sz c h)).sampleOf S .point xp).question hsz .point)
      ((((regsAt P o sz c h)).sampleOf S .dline xq).question hsz .dline) (.values av) (.dpolys f) := by
  simp only [ldB, dirB, show (2 : ℕ) ≠ 1 by decide, if_false, seedOf_blocksV hk P o sz jw c h]
  rw [dir_blocksV hk P o sz c h, pt_blocksV hk P o sz c h, pt_blocksV hk P o sz c h,
    selDirL_vecBits hk o sz jw c S hjw hχ]
  have hmap := ptMapL_vecBits hk o sz jw c S hjw hχ .dline
  simp only [tyNat] at hmap
  rw [hmap, lvpB_eq hk]
  simp only [LIDT.CL.accepts, Sample.question, Regs.sampleOf, Question.fmtOk, subtests,
    Bool.true_and, S.chi_π]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k) {P : PcpParams}
/-- A point answer of the sixth copy is its `m' + 6` blocks. -/
theorem ansB_val6 {i : Fin 6} (hi : (i : ℕ) = 5) {u : Ans P ((shoupBinField k hk)).carrier}
    (hu : ansFmt (i, .point) u = true) :
    ∃ av : Fin (P.m' + 6) → ((shoupBinField k hk)).carrier, u = .inr (.values av) ∧ ansB hk u = ((shoupBinField k hk)).vecBits av ∧
      vals6 u = av ∧ ∀ j, val6 j u = av j := by
  rcases u with (av | f | f) | (av | f | f) <;>
    simp [ansFmt, tyFmt, hi] at hu
  refine ⟨av, rfl, ?_, rfl, fun _ => rfl⟩
  simp [ansB, elems, BinField.vecBits]
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable (F : PcpFamily) (n : ℕ)
theorem _root_.solution {i : Fin 6} (hi : (i : ℕ) = 5) {τ' : LIDT.CL.Ty} (hτ' : τ' ≠ .point)
    {u v : Ans (F.par n) (fld (F.par n) (F.hk n)).carrier} (hu : ansFmt (i, .point) u = true)
    (hv : ansFmt (i, τ') v = true) (x y : Coord (F.par n) → (fld (F.par n) (F.hk n)).carrier) :
    LIDT.CL.accepts (pow_dvd_card _ _ _ _ (F.m'_eq n) (F.jm'_le n))
      (q6 (F.sel' n) .point x) (q6 (F.sel' n) τ' y) (ans6 u) (ans6 v) =
      ldB (unary (F.par n).k) (F.desc n 5) (tyNat τ') (blocksV (F.hk n) (F.par n) x) (blocksV (F.hk n) (F.par n) y)
        (chunks (width (F.par n).m' τ') ((F.par n).m' + 6) (ansB (F.hk n) v)) (ansB (F.hk n) u) := by
  obtain ⟨av, rfl, hua, -, -⟩ := ansB_val6 (F.hk n) hi hu
  rw [hua, F.desc_ge n 5 (by decide)]
  simp only [q6, regs6_eq, ans6]
  cases τ' with
  | point => exact absurd rfl hτ'
  | aline =>
    rcases v with (bv | f | f) | (bv | f | f) <;> simp [ansFmt, tyFmt, hi] at hv
    have hvb : chunks (width (F.par n).m' .aline) ((F.par n).m' + 6) (ansB (F.hk n) (.inr (.apolys f) :
        Ans (F.par n) (fld (F.par n) (F.hk n)).carrier)) = List.ofFn fun c => (fld (F.par n) (F.hk n)).vecBits (f c) := by
      simp only [ansB, elems, List.map_ofFn, width, if_true, Function.comp_def]
      simpa only [BinField.vecBits, List.map_ofFn, Function.comp_def] using
        chunks_ofFn _ _ fun c j => (fld (F.par n) (F.hk n)).toBits (f c j)
    rw [hvb]
    exact (ldB_aline (F.hk n) (F.par n) _ _ _ _ _ (F.jm'_le n) (F.m'_eq n) (F.sel' n)
      (powSel_χ _ _ _ _ _ _) x y av f).symm
  | dline =>
    rcases v with (bv | f | f) | (bv | f | f) <;> simp [ansFmt, tyFmt, hi] at hv
    have hvb : chunks (width (F.par n).m' .dline) ((F.par n).m' + 6) (ansB (F.hk n) (.inr (.dpolys f) :
        Ans (F.par n) (fld (F.par n) (F.hk n)).carrier)) = List.ofFn fun c => (fld (F.par n) (F.hk n)).vecBits (f c) := by
      simp only [ansB, elems, List.map_ofFn, width, reduceCtorEq, if_false, Function.comp_def]
      simpa only [BinField.vecBits, List.map_ofFn, Function.comp_def] using
        chunks_ofFn _ _ fun c j => (fld (F.par n) (F.hk n)).toBits (f c j)
    rw [hvb]
    exact (ldB_dline (F.hk n) (F.par n) _ _ _ _ _ (F.jm'_le n) (F.sel' n)
      (powSel_χ _ _ _ _ _ _) x y av f).symm
end MIPRE.AnswerReduction

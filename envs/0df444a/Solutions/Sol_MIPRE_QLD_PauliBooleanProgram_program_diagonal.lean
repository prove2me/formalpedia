-- Prove2me | solution 1 for MIPRE.QLD.PauliBooleanProgram.program_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T07:01:25.994645+00:00
-- url     : https://prove2.me/submissions/13f8a5d7-04a1-47d7-a25b-09764f16f939

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/PauliBooleanCorrect.lean (solution of MIPRE.QLD.PauliBooleanProgram.program_diagonal);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Basic
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
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
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTrace
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixInverse
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySquareRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculant
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra_B
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg_B
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
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace_B
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_Foundations_SAT_TraceGram
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Foundations_SAT_NormalGram
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusAction
import Definitions.Def_MIPRE_Foundations_SAT_NormalElement
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusMatrix
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusActionProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Definitions.Def_MIPRE_Foundations_Introspection_LineRepresentativeProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Introspection_SeededLineProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_SAT_BasisTransport
import Definitions.Def_MIPRE_Foundations_SAT_EffectiveSelfDual
import Definitions.Def_MIPRE_Foundations_SAT_EffectiveNormalBasis
import Definitions.Def_MIPRE_Foundations_Introspection_BasisProg
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Introspection_FieldPolynomialProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldLineCheckProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg_B
import Definitions.Def_MIPRE_Foundations_Introspection_FieldQuestionProg
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_SAT_PcpFormat
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
import Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParserSlice
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Background_QLD_CLExplicitSeed
import Definitions.Def_MIPRE_Background_QLD_PauliStagePrograms
import Definitions.Def_MIPRE_Background_QLD_TypeEncoding
import Definitions.Def_MIPRE_Foundations_Introspection_FieldAnswerParserProg
import Definitions.Def_MIPRE_Background_QLD_PauliAnswerPrograms
import Definitions.Def_MIPRE_Foundations_Introspection_FieldIndicatorProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldTableProg
import Definitions.Def_MIPRE_Background_QLD_PauliAnswerCoding
import Definitions.Def_MIPRE_Background_QLD_PauliBranchPrograms
import Definitions.Def_MIPRE_Foundations_Introspection_FieldGammaProg
import Definitions.Def_MIPRE_Background_QLD_PauliArithmeticPrograms
import Definitions.Def_MIPRE_Background_QLD_PauliBooleanPrograms
import Definitions.Def_MIPRE_Background_QLD_PauliBooleanCorrect
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_Introspection_FieldLineCheck_parameter_eq
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits
import Theorems.Thm_MIPRE_SAT_BinField_width_vecBits
import Theorems.Thm_MIPRE_SAT_shoupBinField_charP
import Theorems.Thm_MIPRE_SAT_shoupInvProg_correct
import Theorems.Thm_MIPRE_SAT_shoupMulProg_encoding

attribute [instance] MIPRE.SAT.shoupBinField_charP

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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

namespace MIPRE.Introspection.BinaryBlock
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram
theorem splitBlocks_length (n k : ℕ) (v : BitStr) : (splitBlocks n k v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [splitBlocks, ih]
end
end MIPRE.Introspection.BinaryBlock

namespace MIPRE.Introspection.BinaryBlock
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram
theorem flattenProg_apply (vs : List BitStr) : flattenProg vs = vs.flatten := rfl
end
end MIPRE.Introspection.BinaryBlock

namespace MIPRE.Introspection.BinaryBlock
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram
theorem splitBlocks_flatten (k : ℕ) (vs : List BitStr)
    (hv : ∀ v ∈ vs, v.length = k) : splitBlocks vs.length k vs.flatten = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hlen := hv v (by simp)
    have ht : (v ++ vs.flatten).take k = v := by rw [← hlen, List.take_left]
    have hd : (v ++ vs.flatten).drop k = vs.flatten := by rw [← hlen, List.drop_left]
    simp only [List.length_cons, splitBlocks, List.flatten_cons, ht, hd]
    rw [ih (fun w hw => hv w (by simp [hw]))]
end
end MIPRE.Introspection.BinaryBlock

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

namespace MIPRE.Introspection.FieldAnswerParser
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryBlock DynamicParser SAT
theorem length_flatten_of_width (rows : List BitStr) (k : ℕ)
    (hw : ∀ row ∈ rows, row.length = k) : rows.flatten.length = rows.length * k := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hr := hw row (by simp)
    have ht := ih (fun r h => hw r (by simp [h]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, hr, ht, Nat.add_mul, one_mul]
    omega
end
end MIPRE.Introspection.FieldAnswerParser

namespace MIPRE.Introspection.FieldAnswerParser
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryBlock DynamicParser SAT
theorem splitBlocks_exact (n k : ℕ) (bs : BitStr) (hlen : bs.length = n * k) :
    (splitBlocks n k bs).flatten = bs ∧
      ∀ row ∈ splitBlocks n k bs, row.length = k := by
  induction n generalizing bs with
  | zero =>
    have hb : bs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    simp [splitBlocks, hb]
  | succ n ih =>
    have hk : k ≤ bs.length := by rw [hlen, Nat.succ_mul]; omega
    have hd : (bs.drop k).length = n * k := by
      rw [List.length_drop, hlen, Nat.succ_mul]
      omega
    obtain ⟨hf, hw⟩ := ih (bs.drop k) hd
    constructor
    · simpa only [splitBlocks, List.flatten_cons, hf] using List.take_append_drop k bs
    · intro row hrow
      rcases List.mem_cons.mp hrow with rfl | hrow
      · simpa only [List.length_take] using Nat.min_eq_left hk
      · exact hw row hrow
end
end MIPRE.Introspection.FieldAnswerParser

namespace MIPRE.Introspection.FieldAnswerParser
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryBlock DynamicParser SAT
theorem readyProg_spec (n : ℕ) (k : Unary) (bs : BitStr) :
    readyProg (n, k, bs) = true ↔
      0 < k.length ∧ (rowsProg (n, k, bs)).length = n ∧
      (∀ row ∈ rowsProg (n, k, bs), row.length = k.length) ∧
      (rowsProg (n, k, bs)).flatten = bs := by
  simp [readyProg, flattenProg_apply, Nat.succ_le_iff]
end
end MIPRE.Introspection.FieldAnswerParser

namespace MIPRE.Introspection.FieldAnswerParser
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryBlock DynamicParser SAT
theorem readyProg_iff_length (n : ℕ) (k : Unary) (bs : BitStr) :
    readyProg (n, k, bs) = true ↔ 0 < k.length ∧ bs.length = n * k.length := by
  rw [readyProg_spec]
  constructor
  · rintro ⟨hk, hn, hw, he⟩
    refine ⟨hk, ?_⟩
    rw [← he, length_flatten_of_width _ _ hw, hn]
  · rintro ⟨hk, hlen⟩
    have hn : n ≤ bs.length := by rw [hlen]; nlinarith
    have hr : rowsProg (n, k, bs) = splitBlocks n k.length bs := by
      rw [rowsProg_apply, Nat.min_eq_left hn]
    obtain ⟨he, hw⟩ := splitBlocks_exact n k.length bs hlen
    exact ⟨hk, by rw [hr, splitBlocks_length], by rwa [hr], by rwa [hr]⟩
end
end MIPRE.Introspection.FieldAnswerParser

namespace MIPRE.Introspection.FieldAnswerParser
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryBlock DynamicParser SAT
theorem parserProg_flatten (rows : List BitStr) (k : ℕ) (hk : 0 < k)
    (hw : ∀ row ∈ rows, row.length = k) :
    parserProg (rows.length, unary k, rows.flatten) = (true, rows) := by
  have hn : rows.length ≤ rows.flatten.length := by
    rw [length_flatten_of_width rows k hw]
    nlinarith
  have hr : rowsProg (rows.length, unary k, rows.flatten) = rows := by
    rw [rowsProg_apply, length_unary, Nat.min_eq_left hn, splitBlocks_flatten k rows hw]
  have ready : readyProg (rows.length, unary k, rows.flatten) = true := by
    rw [readyProg_iff_length]
    exact ⟨by simpa using hk, by simpa using length_flatten_of_width rows k hw⟩
  change (readyProg _, rowsProg _) = _
  rw [ready, hr]
end
end MIPRE.Introspection.FieldAnswerParser

namespace MIPRE.QLD.PauliAnswerProgram
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT Introspection.FieldAnswerParser
theorem countProg_apply (T : Ty) (m k d : Unary) (bs : BitStr) :
    countProg (T, m, k, d, bs) = count T m.length d.length := by
  cases T <;> simp [countProg, isKind, kind, shape, count, degree, dimension,
    productUnary_length]
end
end MIPRE.QLD.PauliAnswerProgram

namespace MIPRE.QLD.PauliAnswerProgram
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT Introspection.FieldAnswerParser
theorem widthProg_length (T : Ty) (m k d : Unary) (bs : BitStr) :
    (widthProg (T, m, k, d, bs)).length = width T k.length := by
  cases T <;> simp [widthProg, shape, fieldWidth, width]
end
end MIPRE.QLD.PauliAnswerProgram

namespace MIPRE.QLD.PauliAnswerProgram
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT Introspection.FieldAnswerParser
/-- Every canonical payload is returned exactly, including the unit-width bit rows. -/
theorem parser_flatten (T : Ty) (m k d : Unary) (rows : List BitStr)
    (hk : 0 < width T k.length) (hn : rows.length = count T m.length d.length)
    (hw : ∀ row ∈ rows, row.length = width T k.length) :
    parser (T, m, k, d, rows.flatten) = (true, rows) := by
  have huw : widthProg (T, m, k, d, rows.flatten) = unary (width T k.length) := by
    rw [← unary_length (widthProg _), widthProg_length]
  change parserProg (countProg _, widthProg _, answer _) = _
  rw [countProg_apply, huw, ← hn]
  exact parserProg_flatten rows _ hk hw
end
end MIPRE.QLD.PauliAnswerProgram

namespace MIPRE.QLD.PauliAnswerProgram
noncomputable section
open Cost SAT LowDegree LowDegree.BinaryLinear Introspection.FieldTableProgram
theorem answerRows_length {k m d : ℕ} (E : BinField k) (q : Question E.carrier m)
    (a : Answer E.carrier m d) (h : q.fmtOk a = true) :
    (answerRows E a).length = count q.ty m d := by
  cases q <;> cases a <;> simp_all [Question.fmtOk, Question.ty, answerRows, count]
end
end MIPRE.QLD.PauliAnswerProgram

namespace MIPRE.QLD.PauliAnswerProgram
noncomputable section
open Cost SAT LowDegree LowDegree.BinaryLinear Introspection.FieldTableProgram
theorem answerRows_width {k m d : ℕ} (E : BinField k) (q : Question E.carrier m)
    (a : Answer E.carrier m d) (h : q.fmtOk a = true) :
    ∀ row ∈ answerRows E a, row.length = width q.ty k := by
  cases q <;> cases a <;> simp_all [Question.fmtOk, Question.ty, answerRows, width]
  all_goals first
    | exact E.length_toBits _
    | exact fun row hrow => E.width_vecBits _ hrow
end
end MIPRE.QLD.PauliAnswerProgram

namespace MIPRE.QLD.PauliAnswerProgram
noncomputable section
open Cost SAT LowDegree LowDegree.BinaryLinear Introspection.FieldTableProgram
theorem parser_answerBits {k m d : ℕ} (E : BinField k) (hk : 0 < k)
    (q : Question E.carrier m) (a : Answer E.carrier m d) (h : q.fmtOk a = true) :
    parser (q.ty, unary m, unary k, unary d, answerBits E a) =
      (true, answerRows E a) := by
  apply parser_flatten
  · cases q <;> simp_all [Question.ty, width]
  · simpa using answerRows_length E q a h
  · simpa using answerRows_width E q a h
end
end MIPRE.QLD.PauliAnswerProgram

namespace MIPRE.QLD.PauliBranchProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem selectProg_apply (r : Route) (checks : List Bool) :
    selectProg (r, checks) = checks.getD r.1 true := rfl
end
end MIPRE.QLD.PauliBranchProgram

namespace MIPRE.QLD.PauliBranchProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem orientProg_apply {α : Type*} [SizedEncoding α] (swap : Bool) (a b : α) :
    orientProg (swap, a, b) = if swap then (b, a) else (a, b) := rfl
end
end MIPRE.QLD.PauliBranchProgram

namespace MIPRE.QLD.PauliBranchProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem formatGuard_apply (ha hb result : Bool) :
    formatGuard (ha, hb, result) = (ha && hb && result) := by
  cases ha <;> cases hb <;> rfl
end
end MIPRE.QLD.PauliBranchProgram

namespace MIPRE.QLD.PauliArithmeticProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Introspection.FieldLineCheck Introspection.FieldTableProgram Introspection.FieldGammaProgram
theorem parameter_eq_lineParam {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m : ℕ} (origin direction point : Fin m → F) :
    parameter origin direction point = LIDT.CL.lineParam origin direction point :=
  parameter_eq origin direction point
end
end MIPRE.QLD.PauliArithmeticProgram

namespace MIPRE.QLD.PauliArithmeticProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Introspection.FieldLineCheck Introspection.FieldTableProgram Introspection.FieldGammaProgram
/-- The executable coefficient/membership check is exactly the Pauli line rule. -/
theorem lineCheckProg_eq_lowDeg (k : ℕ) (hk : 1 ≤ k) {m n : ℕ}
    (origin direction point : Fin m → (shoupBinField k hk).carrier)
    (f : LIDT.LinePoly (shoupBinField k hk).carrier n)
    (a : (shoupBinField k hk).carrier) :
    lineCheckProg ((unary k, (shoupBinField k hk).vecBits origin,
      (shoupBinField k hk).vecBits direction, (shoupBinField k hk).vecBits point),
      (shoupBinField k hk).vecBits f, (shoupBinField k hk).toBits a) =
      lowDeg origin direction point f a := by
  apply Bool.eq_iff_iff.mpr
  rw [lineCheckProg_correct]
  simp only [lowDeg, LIDT.CL.lineVsPoint, decide_eq_true_eq,
    LIDT.LinePoly.eval, parameter_eq_lineParam]
  simp
end
end MIPRE.QLD.PauliArithmeticProgram

namespace MIPRE.QLD.PauliBooleanProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryLinear Introspection.PauliStageProgram Introspection.FieldLineCheck Introspection.FieldGammaProgram PauliArithmeticProgram
open LCS.MagicSquare
theorem program_apply (input : Input) : program input =
    ((leftParser input).1 && (rightParser input).1 &&
      [consistency input, axisCheck input, diagonalCheck input, tableCheck input,
        pairCheck input, probeCheck input, magicCheck input, magicProbeCheck input].getD
          (route input).1 true) := by
  simp only [program, comp_apply, pair_apply, fst_apply,
    PauliBranchProgram.formatGuard_apply, PauliBranchProgram.selectProg_apply,
    checks, cons_apply, const_apply]
end
end MIPRE.QLD.PauliBooleanProgram

namespace MIPRE.QLD.PauliQuestionProgram
noncomputable section
open Cost SAT Introspection.FieldQuestionProgram Introspection.SeedProgram PauliCL PauliBranchProgram
theorem selectedPoint_fieldEncoding {k m : ℕ} (E : BinField k) (W : Bas)
    (x : Coord m → E.carrier) :
    selectedPoint (MIPRE.QLD.PauliBranchProgram.basisIndex W, fieldEncoding E x) =
      E.vecBits (fun i => x (.point W i)) := by
  cases W <;> rfl
end
end MIPRE.QLD.PauliQuestionProgram

namespace MIPRE.QLD.PauliBooleanProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryLinear PauliCL PauliAnswerProgram PauliQuestionProgram PauliArithmeticProgram
theorem parser_for_type {k m : ℕ} (E : BinField k) (hk : 0 < k)
    (π : E.carrier ≃ E.carrier) (T : Ty) (x : Coord m → E.carrier)
    (a : Answer E.carrier m 1) (ha : (ExplicitSeed.decode π T x).fmtOk a = true) :
    PauliAnswerProgram.parser (T, unary m, unary k, unary 1, answerBits E a) =
      (true, answerRows E a) := by
  simpa using parser_answerBits E hk (ExplicitSeed.decode π T x) a ha
end
end MIPRE.QLD.PauliBooleanProgram

namespace MIPRE.QLD.PauliBooleanProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryLinear PauliCL PauliAnswerProgram PauliQuestionProgram PauliArithmeticProgram
theorem leftParser_encodedInput {k m : ℕ} (E : BinField k) (hk : 0 < k) (j : ℕ)
    (π : E.carrier ≃ E.carrier) (T U : Ty) (x y : Coord m → E.carrier)
    (a b : Answer E.carrier m 1)
    (ha : (ExplicitSeed.decode π T x).fmtOk a = true)
    (hb : (ExplicitSeed.decode π U y).fmtOk b = true) :
    (leftParser (encodedInput E j T U x y a b)).1 = true := by
  have hpa := parser_for_type E hk π T x a ha
  have hpb := parser_for_type E hk π U y b hb
  cases hs : (PauliBranchProgram.route T U).2.1 <;>
    simp [leftParser, leftBits, left, oriented, PauliBranchProgram.orientProg_apply,
      encodedInput, endpoints, dim, width, params, route, endpointTypes, hs, hpa, hpb]
end
end MIPRE.QLD.PauliBooleanProgram

namespace MIPRE.QLD.PauliBooleanProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryLinear PauliCL PauliAnswerProgram PauliQuestionProgram PauliArithmeticProgram
theorem rightParser_encodedInput {k m : ℕ} (E : BinField k) (hk : 0 < k) (j : ℕ)
    (π : E.carrier ≃ E.carrier) (T U : Ty) (x y : Coord m → E.carrier)
    (a b : Answer E.carrier m 1)
    (ha : (ExplicitSeed.decode π T x).fmtOk a = true)
    (hb : (ExplicitSeed.decode π U y).fmtOk b = true) :
    (rightParser (encodedInput E j T U x y a b)).1 = true := by
  have hpa := parser_for_type E hk π T x a ha
  have hpb := parser_for_type E hk π U y b hb
  cases hs : (PauliBranchProgram.route T U).2.1 <;>
    simp [rightParser, rightBits, right, oriented, PauliBranchProgram.orientProg_apply,
      encodedInput, endpoints, dim, width, params, route, endpointTypes, hs, hpa, hpb]
end
end MIPRE.QLD.PauliBooleanProgram

namespace MIPRE.QLD.PauliBooleanProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryLinear PauliCL PauliAnswerProgram PauliQuestionProgram PauliArithmeticProgram
theorem program_of_formatted {k m : ℕ} (E : BinField k) (hk : 0 < k) (j : ℕ)
    (π : E.carrier ≃ E.carrier) (T U : Ty) (x y : Coord m → E.carrier)
    (a b : Answer E.carrier m 1)
    (ha : (ExplicitSeed.decode π T x).fmtOk a = true)
    (hb : (ExplicitSeed.decode π U y).fmtOk b = true) :
    let input := encodedInput E j T U x y a b
    program input = [consistency input, axisCheck input, diagonalCheck input,
      tableCheck input, pairCheck input, probeCheck input, magicCheck input,
      magicProbeCheck input].getD (PauliBranchProgram.route T U).1 true := by
  dsimp only
  rw [program_apply, leftParser_encodedInput E hk j π T U x y a b ha hb,
    rightParser_encodedInput E hk j π T U x y a b ha hb, route_encodedInput]
  simp only [Bool.true_and]
end
end MIPRE.QLD.PauliBooleanProgram

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.PauliBooleanProgram
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryLinear PauliCL PauliAnswerProgram PauliQuestionProgram PauliArithmeticProgram
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) (j m : ℕ) (W : Bas)
    (x y : Coord m → (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) (f : LIDT.LinePoly (shoupBinField k hk).carrier (m * 1)) :
    program (encodedInput (shoupBinField k hk) j (.point W) (.dline W) x y (.val a) (.dpoly f)) =
      lowDeg (fun i => y (.point W i)) (fun i => y (.direction i))
        (fun i => x (.point W i)) f a := by
  have hpa := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.point W) x (.val a) rfl
  have hpb := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.dline W) y (.dpoly f) rfl
  rw [program_of_formatted (shoupBinField k hk) hk j (Equiv.refl _)
    (.point W) (.dline W) x y (.val a) (.dpoly f) rfl rfl]
  have hr : PauliBranchProgram.route (.point W) (.dline W) =
      (2, false, PauliBranchProgram.basisIndex W, 0) := by
    simp [PauliBranchProgram.route, PauliBranchProgram.pairRoute]
  rw [hr]
  change diagonalCheck _ = _
  simp only [diagonalCheck, comp_apply, pair_apply, width, params, origin, point,
    leftValue, leftRows, rightRows, leftParser, rightParser, leftBits, rightBits,
    leftFields, rightFields, left, right, oriented, basis, route, endpointTypes,
    endpoints, encodedInput, fst_apply, snd_apply, dim, const_apply,
    PauliBranchProgram.routeProg_apply, hr, PauliBranchProgram.orientProg_apply,
    Bool.false_eq_true, ↓reduceIte, hpa, hpb, nthD_apply,
    PauliAnswerProgram.answerRows, List.getD_cons_zero,
    selectedPoint_fieldEncoding, direction_fieldEncoding, lineCheckProg_eq_lowDeg k hk]
end MIPRE.QLD.PauliBooleanProgram

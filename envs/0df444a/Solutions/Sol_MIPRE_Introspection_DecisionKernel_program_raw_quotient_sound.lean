-- Prove2me | solution 1 for MIPRE.Introspection.DecisionKernel.program_raw_quotient_sound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T07:45:33.612991+00:00
-- url     : https://prove2.me/submissions/37911243-1e68-4a18-b548-b1c80a6770a5

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/DecisionKernelAuxiliary.lean (solution of MIPRE.Introspection.DecisionKernel.program_raw_quotient_sound);
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
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
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
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
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
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
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
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_FiniteEncoding
import Definitions.Def_MIPRE_Foundations_Introspection_FieldPolynomialProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldLineCheckProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg_B
import Definitions.Def_MIPRE_Foundations_Introspection_FieldQuestionProg
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_SAT_PcpFormat
import Definitions.Def_MIPRE_Foundations_Cost_FiniteChoice
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingClock
import Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Introspection_ClockArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
import Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParserSlice
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParser
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParams
import Definitions.Def_MIPRE_Foundations_Introspection_PauliSamplerParams
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulationCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_PauliSamplerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
import Definitions.Def_MIPRE_Foundations_Introspection_ParserGuard
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerCost
import Definitions.Def_MIPRE_Foundations_Introspection_DecisionPreparation
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
import Definitions.Def_MIPRE_Background_QLD_BinaryBlocks
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRowsProg
import Definitions.Def_MIPRE_Background_QLD_PauliBinaryPrograms
import Definitions.Def_MIPRE_Background_QLD_PauliBooleanCorrect
import Definitions.Def_MIPRE_Background_QLD_PauliBooleanSymmetry
import Definitions.Def_MIPRE_Background_QLD_PauliBooleanDispatch
import Definitions.Def_MIPRE_Background_QLD_PauliAnswerRoundtrip
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_WeylBinary
import Definitions.Def_MIPRE_Background_QLD_PauliFullAnswerPrograms
import Definitions.Def_MIPRE_Background_QLD_PauliFullAnswerCorrect
import Definitions.Def_MIPRE_Background_QLD_PauliBinaryInterface
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryReadProgram
import Definitions.Def_MIPRE_Background_Introspection_DecisionKernelInput
import Definitions.Def_MIPRE_Foundations_Introspection_ClockedQueryProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySamplingProgram
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePadding
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryRegisterBits
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySamplingCorrect
import Definitions.Def_MIPRE_Foundations_Introspection_ClockedSourceChecks
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizerIdeal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixFactor
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryPrefixSolve
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryMaskProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientChecks
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryHidingCoreProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySourceQueries
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanStage
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanCorrect
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryRegisterProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryHidingNextProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryHidingBoundaryProgram
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingQueries
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingQueryProg
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDecisionProgram
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingQueryCorrect
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixGuard
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryPrefixGuardProgram
import Definitions.Def_MIPRE_Foundations_Introspection_GuardedAuxiliaryProgram
import Definitions.Def_MIPRE_Background_Introspection_DecisionKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDecisionCorrect
import Definitions.Def_MIPRE_Background_Introspection_DecisionKernelCanonical
import Definitions.Def_MIPRE_Foundations_Introspection_TypedQuotientPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryAnswerCoding
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDecisionSoundness
import Definitions.Def_MIPRE_Foundations_Introspection_ParsedPauliTransport
import Definitions.Def_MIPRE_Foundations_Introspection_BoundedAnswerCoding
import Definitions.Def_MIPRE_Background_Introspection_DecisionKernelAnswers
import Definitions.Def_MIPRE_Background_Introspection_DecisionKernelAuxiliary
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_CL_Detyping_toBits_zero
import Theorems.Thm_MIPRE_Introspection_AuxiliaryDecision_check_raw_sound
import Theorems.Thm_MIPRE_Introspection_AuxiliaryDecision_guarded_iff
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_equal_iff
import Theorems.Thm_MIPRE_Introspection_DecisionKernel_program_auxiliary_facts
import Theorems.Thm_MIPRE_Introspection_SourceCompiler_bounded_dimensionResult
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_groupComponentsProg_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_inverseRootMatrixProg_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_mulBits_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_transposeBits_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits
import Theorems.Thm_MIPRE_QLD_PauliAnswerProgram_answerRows_decodeRows
import Theorems.Thm_MIPRE_QLD_PauliBooleanProgram_program_correct_formatted
import Theorems.Thm_MIPRE_QLD_PauliCL_binaryVectorEquiv_bits
import Theorems.Thm_MIPRE_SAT_BinField_width_vecBits
import Theorems.Thm_MIPRE_SAT_shoupActionProg_correct
import Theorems.Thm_MIPRE_SAT_shoupBinField_finrank
import Theorems.Thm_MIPRE_SAT_shoupBinField_toBits_ofBits
import Theorems.Thm_MIPRE_SAT_shoupInBasisProg_correct
import Theorems.Thm_MIPRE_SAT_shoupMulProg_encoding
import Theorems.Thm_MIPRE_SAT_shoupNormalBasis_normal
import Theorems.Thm_MIPRE_SAT_shoupTraceGramProg_correct

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_injective : Function.Injective (ofBool : Bool → ZMod 2) := by
  intro a b h
  have := congrArg bit h
  simpa using this
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_xor (a b : Bool) :
    (ofBool (a ^^ b) : ZMod 2) = ofBool a + ofBool b := by
  cases a <;> cases b <;> decide
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_and (a b : Bool) :
    (ofBool (a && b) : ZMod 2) = ofBool a * ofBool b := by
  cases a <;> cases b <;> decide
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_fold_dotStep (l : List (Bool × Bool)) (b : Bool) :
    (ofBool (l.foldl dotStep b) : ZMod 2) =
      ofBool b + (l.map (fun p => (ofBool p.1 : ZMod 2) * ofBool p.2)).sum := by
  induction l generalizing b with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    simp only [dotStep, ofBool_xor, ofBool_and, List.map_cons, List.sum_cons]
    ring
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_dotBits (a b : BitStr) :
    (ofBool (dotBits a b) : ZMod 2) =
      ((a.zip b).map (fun p => (ofBool p.1 : ZMod 2) * ofBool p.2)).sum := by
  rw [dotBits, ofBool_fold_dotStep]
  simp [ofBool]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem zip_vectorBits {n : ℕ} (v w : Fin n → ZMod 2) :
    (vectorBits v).zip (vectorBits w) = List.ofFn (fun i => (bit (v i), bit (w i))) := by
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    simp [vectorBits]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
/-- The raw parity circuit computes the exact binary dot product. -/
theorem dotBits_vectorBits {n : ℕ} (v w : Fin n → ZMod 2) :
    dotBits (vectorBits v) (vectorBits w) = bit (∑ i, v i * w i) := by
  apply ofBool_injective
  rw [ofBool_dotBits, zip_vectorBits, ofBool_bit]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, ofBool_bit]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
/-- Executable matrix application agrees with the usual binary matrix-vector product. -/
theorem applyBits_matrixBits {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) :
    applyBits (matrixBits A) (vectorBits v) = vectorBits (A.mulVec v) := by
  simp only [applyBits, matrixBits, List.map_ofFn, vectorBits]
  apply congrArg List.ofFn
  funext i
  exact dotBits_vectorBits (A i) v
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem unitBits_eq_vectorBits {n : ℕ} (j : Fin n) :
    unitBits n j = vectorBits (Pi.single j 1 : Fin n → ZMod 2) := by
  apply List.ext_getElem
  · simp [unitBits, vectorBits]
  · intro i hi hj
    simp only [unitBits, vectorBits, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    by_cases he : i = j
    · simp [bit, Pi.single_apply, Fin.ext_iff, he]
    · simp [bit, Pi.single_apply, Fin.ext_iff, he]
end
end MIPRE.LowDegree.BinaryLinear

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
open Cost LowDegree LowDegree.BinaryPolynomial LowDegree.BinaryLinear
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_1
/-- Standard unit vectors encode the corresponding polynomial-basis elements. -/
theorem shoupPowerBasis_encoding (k : ℕ) (hk : 1 ≤ k) (j : Fin k) :
    (shoupBinField k hk).toBits (shoupPowerBasis k hk j) = unitBits k j := by
  rw [← shoupCoordinateEquiv_encoding, shoupPowerBasis, Module.Basis.coe_ofEquivFun,
    LinearEquiv.apply_symm_apply, unitBits_eq_vectorBits]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear LowDegree.BinaryPolynomial
theorem shoupSquareProg_correct (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) :
    shoupSquareProg (unary k, (shoupBinField k hk).toBits a) =
      (shoupBinField k hk).toBits (shoupFrobeniusLinear k hk a) := by
  change shoupMulProg (unary k, (shoupBinField k hk).toBits a,
    (shoupBinField k hk).toBits a) = _
  rw [shoupMulProg_encoding, shoupFrobeniusLinear_apply, pow_two]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
theorem shoupSquareStateProg_iterate_correct (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) (n : ℕ) :
    ((shoupSquareStateProg : (Unary × BitStr) → (Unary × BitStr))^[n]
      (unary k, (shoupBinField k hk).toBits a)) =
    (unary k, (shoupBinField k hk).toBits (a ^ (2 ^ n))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change (unary k, shoupSquareProg (unary k, (shoupBinField k hk).toBits (a ^ (2 ^ n)))) = _
    rw [shoupSquareProg_correct, shoupFrobeniusLinear_apply, ← pow_mul, ← pow_succ]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
theorem shoupOrbitProg_correct (k : ℕ) (hk : 1 ≤ k) (a : (shoupBinField k hk).carrier) :
    shoupOrbitProg (unary k, (shoupBinField k hk).toBits a) =
      List.ofFn (fun i : Fin k => (shoupBinField k hk).toBits (a ^ (2 ^ i.val))) := by
  change (recordIterates (shoupSquareStateProg : (Unary × BitStr) → (Unary × BitStr))
    (unary k) (unary k, (shoupBinField k hk).toBits a)).map Prod.snd = _
  simp only [recordIterates, length_unary, List.map_ofFn, shoupSquareStateProg_iterate_correct]
  rfl
end
end MIPRE.SAT

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
theorem arithmeticFold_cons (mul : Bool) (p a b : BitStr) (l : List BitStr) :
    arithmeticFold mul p a (b :: l) =
      arithmeticFold mul p (if mul then mulReduce p a b else xorBits a b) l := rfl
end
end MIPRE.LowDegree.BinaryPolynomial

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

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem firstNonzeroBitsProg_correct (k : ℕ) (hk : 1 ≤ k)
    (l : List (shoupBinField k hk).carrier) :
    firstNonzeroBitsProg (l.map (shoupBinField k hk).toBits, (shoupBinField k hk).toBits 0) =
      (shoupBinField k hk).toBits (firstNonzero l) := by
  change (l.map (shoupBinField k hk).toBits).foldr
    (fun a s => if nonzeroRow a then a else s) _ = _
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.foldr_cons, shoupNonzeroRow_correct, ih]
    by_cases ha : a = 0 <;> simp [ha, firstNonzero]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupProjectionImagesProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (e : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    shoupProjectionImagesProg (unary k, vectorBits (groupCoordinates k e)) =
      List.ofFn (fun j => (shoupBinField k hk).toBits
        (shoupFrobeniusAction k hk e (shoupPowerBasis k hk j))) := by
  have hu : identityBits k = List.ofFn (fun j => (shoupBinField k hk).toBits (shoupPowerBasis k hk j)) := by
    apply List.ext_getElem
    · simp [identityBits]
    · intro j hj hj'
      have hjk : j < k := by simpa [identityBits] using hj
      simp only [identityBits, List.getElem_map, List.getElem_range, List.getElem_ofFn]
      exact (shoupPowerBasis_encoding k hk (⟨j, hjk⟩ : Fin k)).symm
  change (identityBits (unary k).length).map
    (fun a => shoupActionProg (unary k, vectorBits (groupCoordinates k e), a)) = _
  rw [length_unary, hu, List.map_ofFn]
  congr 1
  funext j
  exact shoupActionProg_correct k hk e _
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupProjectedVectorProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (e : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    shoupProjectedVectorProg (unary k, vectorBits (groupCoordinates k e)) =
      (shoupBinField k hk).toBits (shoupProjectedVector k hk e) := by
  change firstNonzeroBitsProg
    (shoupProjectionImagesProg (unary k, vectorBits (groupCoordinates k e)),
      shoupZeroProg (unary k)) = _
  rw [shoupProjectionImagesProg_correct k hk, shoupZeroProg_correct k hk]
  rw [show List.ofFn (fun j => (shoupBinField k hk).toBits
      (shoupFrobeniusAction k hk e (shoupPowerBasis k hk j))) =
    (List.ofFn (fun j => shoupFrobeniusAction k hk e (shoupPowerBasis k hk j))).map
      (shoupBinField k hk).toBits by rw [List.map_ofFn]; rfl]
  exact firstNonzeroBitsProg_correct k hk _
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupArithmeticFold_add_correct (k : ℕ) (hk : 1 ≤ k)
    (l : List (shoupBinField k hk).carrier) (a : (shoupBinField k hk).carrier) (p : BitStr) :
    BinaryPolynomial.arithmeticFold false p ((shoupBinField k hk).toBits a)
      (l.map (shoupBinField k hk).toBits) = (shoupBinField k hk).toBits (a + l.sum) := by
  induction l generalizing a with
  | nil => simp [BinaryPolynomial.arithmeticFold]
  | cons b l ih =>
    rw [List.map_cons, BinaryPolynomial.arithmeticFold_cons]
    simp only [Bool.false_eq_true, if_false]
    rw [shoupXorBits_correct, ih, List.sum_cons, add_assoc]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupSumProg_correct (k : ℕ) (hk : 1 ≤ k) (l : List (shoupBinField k hk).carrier) :
    shoupSumProg (unary k, l.map (shoupBinField k hk).toBits) =
      (shoupBinField k hk).toBits l.sum := by
  change BinaryPolynomial.arithmeticFold false (shoupZeroProg (unary k))
    (shoupZeroProg (unary k)) (l.map (shoupBinField k hk).toBits) = _
  rw [shoupZeroProg_correct k hk, shoupArithmeticFold_add_correct, zero_add]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupNormalElementProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] :
    shoupNormalElementProg (unary k) = (shoupBinField k hk).toBits (shoupNormalElement k hk) := by
  change shoupSumProg (unary k, (groupComponentsProg (unary k)).map
    (fun e => shoupProjectedVectorProg (unary k, e))) = _
  rw [groupComponentsProg_correct, List.map_map]
  simp only [Function.comp_def, shoupProjectedVectorProg_correct k hk]
  rw [show (groupComponents k).map (fun e => (shoupBinField k hk).toBits (shoupProjectedVector k hk e)) =
    ((groupComponents k).map (shoupProjectedVector k hk)).map (shoupBinField k hk).toBits by
      rw [List.map_map]; rfl, shoupSumProg_correct]
  congr 1
  simp [shoupNormalElement, List.get_eq_getElem]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupNormalBasisProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    shoupNormalBasisProg (unary k) =
      List.ofFn (fun i => (shoupBinField k hk).toBits (shoupNormalBasis k hk hodd i)) := by
  change shoupOrbitProg (unary k, shoupNormalElementProg (unary k)) = _
  rw [shoupNormalElementProg_correct k hk, shoupOrbitProg_correct]
  simp only [shoupNormalBasis_apply]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear
/-- The supplied basis vectors are exactly the columns of the change-of-basis matrix. -/
theorem shoupBasisMatrix_encoding (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier) :
    transposeBits k (List.ofFn (fun i => (shoupBinField k hk).toBits (b i))) =
      matrixBits (shoupBasisMatrix k hk b) := by
  have hc : List.ofFn (fun i => (shoupBinField k hk).toBits (b i)) =
      matrixBits (shoupBasisMatrix k hk b).transpose := by
    apply congrArg List.ofFn
    funext j
    rw [← shoupCoordinateEquiv_encoding]
    congr 1
    funext i
    exact (LinearMap.toMatrix_apply b (shoupPowerBasis k hk) LinearMap.id i j).symm
  rw [hc, transposeBits_matrixBits, Matrix.transpose_transpose]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear
/-- Matrix application sends the new coordinates to the original coordinates. -/
theorem shoupBasisMatrix_mulVec (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) :
    (shoupBasisMatrix k hk b).mulVec (b.equivFun a) = shoupCoordinateEquiv k hk a :=
  LinearMap.toMatrix_mulVec_repr b (shoupPowerBasis k hk) LinearMap.id a
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear
theorem shoupSelfDualBasis_apply (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) (i : Fin k) :
    shoupSelfDualBasis k hk hodd b hb i = shoupSelfDualVectors k hk b i := by
  rw [shoupSelfDualBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear
/-- Polynomial-basis coordinates of the changed family are the matrix product columns. -/
theorem shoupChangedVectors_encoding (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (H : Matrix (Fin k) (Fin k) (ZMod 2)) (j : Fin k) :
    (shoupBinField k hk).toBits (shoupChangedVectors k hk b H j) =
      vectorBits ((shoupBasisMatrix k hk b * H).col j) := by
  rw [← shoupCoordinateEquiv_encoding]
  congr 1
  funext i
  simp only [shoupChangedVectors, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.col_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [shoupBasisMatrix, LinearMap.toMatrix_apply]
  exact mul_comm _ _
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear
/-- Every output vector is the canonical encoding of the constructed self-dual normal basis. -/
theorem shoupSelfDualizeProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) :
    shoupSelfDualizeProg (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i))) =
      List.ofFn (fun i => (shoupBinField k hk).toBits (shoupSelfDualBasis k hk hodd b hb i)) := by
  change transposeBits (unary k).length (mulBits (unary k).length
    (transposeBits (unary k).length (List.ofFn (fun i => (shoupBinField k hk).toBits (b i))))
    (inverseRootMatrixProg (unary k, shoupTraceGramProg
      (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i)))))) = _
  rw [length_unary, shoupBasisMatrix_encoding, shoupTraceGramProg_correct,
    inverseRootMatrixProg_correct hodd, mulBits_matrixBits, transposeBits_matrixBits]
  apply congrArg List.ofFn
  funext i
  rw [shoupSelfDualBasis_apply]
  exact (shoupChangedVectors_encoding k hk b _ i).symm
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_7
theorem shoupSelfDualNormalBasisProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    shoupSelfDualNormalBasisProg (unary k) =
      List.ofFn (fun i => (shoupBinField k hk).toBits (shoupSelfDualNormalBasis k hk hodd i)) := by
  change shoupSelfDualizeProg (unary k, shoupNormalBasisProg (unary k)) = _
  rw [shoupNormalBasisProg_correct k hk hodd,
    shoupSelfDualizeProg_correct k hk hodd _ (shoupNormalBasis_normal k hk hodd)]
  rfl
end
end MIPRE.SAT

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem fromBasisProg_correct (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) :
    fromBasisProg (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i)),
      vectorBits (b.equivFun a)) = (shoupBinField k hk).toBits a := by
  change applyBits (transposeBits (unary k).length
    (List.ofFn fun i => (shoupBinField k hk).toBits (b i))) (vectorBits (b.equivFun a)) = _
  rw [length_unary, shoupBasisMatrix_encoding, applyBits_matrixBits,
    shoupBasisMatrix_mulVec, shoupCoordinateEquiv_encoding]
end
end MIPRE.Introspection.BasisProgram

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem toSelfDualProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (a : (shoupBinField k hk).carrier) :
    toSelfDualProg (unary k, (shoupBinField k hk).toBits a) =
      vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun a) := by
  change shoupInBasisProg (unary k, shoupSelfDualNormalBasisProg (unary k),
    (shoupBinField k hk).toBits a) = _
  rw [shoupSelfDualNormalBasisProg_correct k hk hodd, shoupInBasisProg_correct]
end
end MIPRE.Introspection.BasisProgram

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem fromSelfDualProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (a : (shoupBinField k hk).carrier) :
    fromSelfDualProg (unary k,
      vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun a)) =
      (shoupBinField k hk).toBits a := by
  change fromBasisProg (unary k, shoupSelfDualNormalBasisProg (unary k),
    vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun a)) = _
  rw [shoupSelfDualNormalBasisProg_correct k hk hodd, fromBasisProg_correct]
end
end MIPRE.Introspection.BasisProgram

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem toSelfDualRowsProg_apply (k : Unary) (vs : List BitStr) :
    toSelfDualRowsProg (k, vs) = vs.map (fun v => toSelfDualProg (k, v)) := rfl
end
end MIPRE.Introspection.BasisProgram

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem fromSelfDualRowsProg_apply (k : Unary) (vs : List BitStr) :
    fromSelfDualRowsProg (k, vs) = vs.map (fun v => fromSelfDualProg (k, v)) := rfl
end
end MIPRE.Introspection.BasisProgram

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem toSelfDualRowsProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {n : ℕ} (u : Fin n → (shoupBinField k hk).carrier) :
    toSelfDualRowsProg (unary k, (shoupBinField k hk).vecBits u) =
      List.ofFn (fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i))) := by
  simp only [toSelfDualRowsProg_apply, BinField.vecBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact toSelfDualProg_correct k hk hodd (u i)
end
end MIPRE.Introspection.BasisProgram

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem fromSelfDualRowsProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {n : ℕ} (u : Fin n → (shoupBinField k hk).carrier) :
    fromSelfDualRowsProg (unary k,
      List.ofFn (fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i)))) =
      (shoupBinField k hk).vecBits u := by
  simp only [fromSelfDualRowsProg_apply, BinField.vecBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact fromSelfDualProg_correct k hk hodd (u i)
end
end MIPRE.Introspection.BasisProgram

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

namespace MIPRE.Introspection.BinaryBlock
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram
theorem decodeBlocksProg_apply (n k : Unary) (v : BitStr) :
    decodeBlocksProg (n, k, v) = fromSelfDualRowsProg (k, splitBlocks n.length k.length v) := rfl
end
end MIPRE.Introspection.BinaryBlock

namespace MIPRE.Introspection.BinaryBlock
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram
theorem encodeBlocksProg_apply (k : Unary) (vs : List BitStr) :
    encodeBlocksProg (k, vs) = (toSelfDualRowsProg (k, vs)).flatten := rfl
end
end MIPRE.Introspection.BinaryBlock

namespace MIPRE.Introspection.BinaryBlock
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram
theorem encodeBlocksProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {n : ℕ} (u : Fin n → (shoupBinField k hk).carrier) :
    encodeBlocksProg (unary k, (shoupBinField k hk).vecBits u) =
      (List.ofFn (fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i)))).flatten := by
  rw [encodeBlocksProg_apply, toSelfDualRowsProg_correct k hk hodd]
end
end MIPRE.Introspection.BinaryBlock

namespace MIPRE.Introspection.BinaryBlock
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram
theorem decodeBlocksProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {n : ℕ} (u : Fin n → (shoupBinField k hk).carrier) :
    decodeBlocksProg (unary n, unary k,
      (List.ofFn (fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i)))).flatten) =
      (shoupBinField k hk).vecBits u := by
  rw [decodeBlocksProg_apply, length_unary, length_unary]
  have he := splitBlocks_flatten k
    (List.ofFn fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i))) (by
      intro v hv
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      simp [vectorBits])
  simp only [List.length_ofFn] at he
  rw [he, fromSelfDualRowsProg_correct k hk hodd]
end
end MIPRE.Introspection.BinaryBlock

namespace MIPRE.CL
section
variable {k s : ℕ}
theorem finProdFinEquiv_val (i : Fin k) (j : Fin s) :
    ((finProdFinEquiv (i, j) : Fin (k * s)) : ℕ) = j + s * i := rfl
end
end MIPRE.CL

namespace MIPRE.CL
section
variable {k s : ℕ}
/-- A list indexed by `Fin (k s)` is the concatenation of its `k` blocks of `s`. -/
theorem ofFn_eq_flatten_blocks {α : Type*} (f : Fin (k * s) → α) :
    List.ofFn f =
      (List.ofFn fun i : Fin k => List.ofFn fun j : Fin s => f (finProdFinEquiv (i, j))).flatten := by
  rw [List.ofFn_mul]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i => congrArg List.ofFn
    (funext fun j => congrArg f (Fin.ext ?_))))
  change (i : ℕ) * s + j = _
  rw [finProdFinEquiv_val]
  ring
end
end MIPRE.CL

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

namespace MIPRE.Introspection.FieldAnswerParser
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryBlock DynamicParser SAT
/-- Canonically encoded field vectors are returned exactly, without padding or loss. -/
theorem parserProg_vecBits {n k : ℕ} (E : BinField k) (hk : 0 < k)
    (v : Fin n → E.carrier) :
    parserProg (n, unary k, (E.vecBits v).flatten) = (true, E.vecBits v) := by
  simpa using parserProg_flatten (E.vecBits v) k hk (fun _ h => E.width_vecBits v h)
end
end MIPRE.Introspection.FieldAnswerParser

namespace MIPRE.Introspection.FieldAnswerParser
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryBlock DynamicParser SAT
theorem fullPauliParserProg_vecBits {m k : ℕ} (E : BinField k) (hk : 0 < k)
    (v : Fin (2 ^ m) → E.carrier) :
    fullPauliParserProg (unary m, unary k, (E.vecBits v).flatten) = (true, E.vecBits v) := by
  change parserProg (1 * 2 ^ (unary m).length, unary k, (E.vecBits v).flatten) = _
  simpa using parserProg_vecBits E hk v
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
open Cost SAT LowDegree LowDegree.BinaryLinear Introspection.FieldTableProgram
theorem decodeRows_format {k m d : ℕ} (E : BinField k) (q : Question E.carrier m)
    (rows : List BitStr) : q.fmtOk (decodeRows E m d q.ty rows) = true := by
  cases q <;> rfl
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
theorem formatGuard_apply (ha hb result : Bool) :
    formatGuard (ha, hb, result) = (ha && hb && result) := by
  cases ha <;> cases hb <;> rfl
end
end MIPRE.QLD.PauliBranchProgram

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

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT LowDegree.BinaryLinear Introspection.BinaryBlock
set_option linter.unusedSectionVars false
theorem numberedRows_length {k m : ℕ} (E : BinField k) (x : Coord m → E.carrier) :
    (numberedRows E x).length = 3 * m + 3 := List.length_ofFn
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT LowDegree.BinaryLinear Introspection.BinaryBlock
set_option linter.unusedSectionVars false
theorem numberedRows_getD {k m : ℕ} (E : BinField k) (x : Coord m → E.carrier)
    (c : Coord m) :
    (numberedRows E x).getD (coordNumbering m c).val [] = E.toBits (x c) := by
  simp only [numberedRows, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    (coordNumbering m c).isLt, dite_true, Option.getD_some, Fin.eta,
    Equiv.symm_apply_apply]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT LowDegree.BinaryLinear Introspection.BinaryBlock
set_option linter.unusedSectionVars false
theorem numberedRows_eq_vecBits {k m : ℕ} (E : BinField k) (x : Coord m → E.carrier) :
    numberedRows E x = E.vecBits (fun i => x ((coordNumbering m).symm i)) := by
  simp only [numberedRows, BinField.vecBits, List.map_ofFn, Function.comp_def]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT LowDegree.BinaryLinear Introspection.BinaryBlock
set_option linter.unusedSectionVars false
/-- The executable decoder returns the exact canonical field row at each
numbered coordinate of the self-dual downsized vector. -/
theorem decodeBlocksProg_binaryVector (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {m : ℕ} [NeZero m] (x : Coord m → (shoupBinField k hk).carrier) :
    decodeBlocksProg (unary (3 * m + 3), unary k,
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x)) =
      numberedRows (shoupBinField k hk) x := by
  rw [binaryVectorEquiv_bits, decodeBlocksProg_correct k hk hodd, numberedRows_eq_vecBits]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT LowDegree.BinaryLinear Introspection.BinaryBlock
set_option linter.unusedSectionVars false
/-- A full-length raw CL bit string is interpreted by the actual inverse
binary coordinate map; no assumption that its bits are polynomial coordinates
is made. -/
theorem decodeBlocksProg_ofBits (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {m : ℕ} [NeZero m] (z : BitStr) (hz : z.length = (3 * m + 3) * k) :
    decodeBlocksProg (unary (3 * m + 3), unary k, z) =
      numberedRows (shoupBinField k hk)
        ((binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd)).symm
          (CL.ofBits ((3 * m + 3) * k) z)) := by
  have he := decodeBlocksProg_binaryVector k hk hodd
    ((binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd)).symm
      (CL.ofBits ((3 * m + 3) * k) z))
  simpa only [LinearEquiv.apply_symm_apply, CL.toBits_ofBits hz] using he
end
end MIPRE.QLD.PauliCL

namespace MIPRE.Introspection.PauliStageProgram
noncomputable section
open Cost Cost.PolyTimeFun
theorem unpackRows_packRows (m : ℕ) (x z : List BitStr) (s : BitStr)
    (v : List BitStr) (rx rz : BitStr)
    (hx : x.length = m) (hz : z.length = m) (hv : v.length = m) :
    unpackRows (unary m, packRows (x, z, s, v, rx, rz)) = (x, z, s, v, rx, rz) := by
  simp [unpackRows, pack, hx, hz, hv]
end
end MIPRE.Introspection.PauliStageProgram

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram
theorem packRows_fieldEncoding_getD {k m : ℕ} (E : BinField k)
    (x : Coord m → E.carrier) (c : Coord m) :
    (packRows (fieldEncoding E x)).getD (coordNumbering m c).val [] = E.toBits (x c) := by
  have hlen (v : Fin m → E.carrier) : (E.vecBits v).length = m := by simp [BinField.vecBits]
  have hget (v : Fin m → E.carrier) (i : Fin m) :
      (E.vecBits v).getD i.val [] = E.toBits (v i) := by
    simp [BinField.vecBits, List.getD_eq_getElem?_getD, i.isLt]
  cases c with
  | point W i =>
    cases W with
    | X =>
      simp only [fieldEncoding, packRows_apply, coordNumbering_point_X]
      rw [List.getD_append _ _ _ _ (by simpa only [hlen] using i.isLt), hget]
    | Z =>
      simp only [fieldEncoding, packRows_apply, coordNumbering_point_Z]
      rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen,
        Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by simpa only [hlen] using i.isLt), hget]
  | seed =>
    simp only [fieldEncoding, packRows_apply, coordNumbering_seed]
    rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen,
      List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen]
    simp [show 2 * m - m - m = 0 by omega]
  | direction i =>
    simp only [fieldEncoding, packRows_apply, coordNumbering_direction]
    rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen,
      List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen]
    rw [show 2 * m + 1 + i.val - m - m = i.val + 1 by omega]
    simp only [List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simpa only [hlen] using i.isLt), hget]
  | scalar W =>
    cases W <;> simp only [fieldEncoding, packRows_apply,
      coordNumbering_scalar_X, coordNumbering_scalar_Z]
    all_goals
      rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen,
        List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen]
    · rw [show 3 * m + 1 - m - m = m + 1 by omega]
      simp only [List.getD_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by simp [hlen]), hlen]
      simp
    · rw [show 3 * m + 2 - m - m = (m + 1) + 1 by omega]
      simp only [List.getD_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen]
      simp
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram
theorem packRows_fieldEncoding {k m : ℕ} (E : BinField k)
    (x : Coord m → E.carrier) : packRows (fieldEncoding E x) = numberedRows E x := by
  have hlen : (packRows (fieldEncoding E x)).length = 3 * m + 3 := by
    simp [packRows, fieldEncoding, pointX, pointZ, seed, direction, scalarX, scalarZ,
      BinField.vecBits]
    omega
  apply List.ext_getElem
  · rw [hlen, numberedRows_length]
  · intro i hi hi'
    have hil : i < 3 * m + 3 := by simpa only [hlen] using hi
    let c := (coordNumbering m).symm ⟨i, hil⟩
    have hc : (coordNumbering m c).val = i := by simp [c]
    have he := (packRows_fieldEncoding_getD E x c).trans (numberedRows_getD E x c).symm
    simpa only [hc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hi', Option.getD_some] using he
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram
theorem unpackRows_numberedRows {k m : ℕ} (E : BinField k)
    (x : Coord m → E.carrier) : unpackRows (unary m, numberedRows E x) = fieldEncoding E x := by
  rw [← packRows_fieldEncoding]
  exact unpackRows_packRows m _ _ _ _ _ _ (by simp [BinField.vecBits])
    (by simp [BinField.vecBits]) (by simp [BinField.vecBits])
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliBinaryProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT PauliCL Introspection.PauliStageProgram Introspection.BinaryBlock
theorem coordinateCount_apply (k j m : Unary) :
    coordinateCount (k, j, m) = unary (3 * m.length + 3) := by
  have hm : m = unary m.length := (unary_length m).symm
  simp only [coordinateCount, ap₂_apply, comp_apply, append_apply,
    snd_apply, const_apply]
  rw [hm]
  simp only [unary, ← List.replicate_add, List.length_replicate]
  congr 1
  omega
end
end MIPRE.QLD.PauliBinaryProgram

namespace MIPRE.QLD.PauliBinaryProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT PauliCL Introspection.PauliStageProgram Introspection.BinaryBlock
/-- Every full-length bit string has exactly its inverse-basis field meaning. -/
theorem fieldsProg_ofBits (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j m : ℕ) [NeZero m] (bs : BitStr) (hbs : bs.length = (3 * m + 3) * k) :
    fieldsProg ((unary k, unary j, unary m), bs) =
      fieldEncoding (shoupBinField k hk)
        ((binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd)).symm
          (CL.ofBits ((3 * m + 3) * k) bs)) := by
  simp only [fieldsProg, comp_apply, pair_apply, fst_apply, snd_apply,
    coordinateCount_apply, length_unary, decodeBlocksProg_ofBits k hk hodd bs hbs,
    unpackRows_numberedRows]
end
end MIPRE.QLD.PauliBinaryProgram

namespace MIPRE.QLD.PauliAnswerProgram
noncomputable section
open Cost SAT LowDegree LowDegree.BinaryLinear Introspection.FieldTableProgram
/-- A successful parser returns the exact count, exact row widths and the original bits. -/
theorem parser_rows_spec (T : Ty) (m k d : ℕ) (bs : BitStr)
    (h : (parser (T, unary m, unary k, unary d, bs)).1 = true) :
    let rows := (parser (T, unary m, unary k, unary d, bs)).2
    rows.length = count T m d ∧
      (∀ row ∈ rows, row.length = width T k) ∧ rows.flatten = bs := by
  have hs := (Introspection.FieldAnswerParser.readyProg_spec
    (countProg (T, unary m, unary k, unary d, bs))
    (widthProg (T, unary m, unary k, unary d, bs)) bs).mp h
  simpa only [parser, Cost.PolyTimeFun.comp_apply, Cost.PolyTimeFun.pair_apply,
    Introspection.FieldAnswerParser.parserProg, answer, Cost.PolyTimeFun.snd_apply,
    countProg_apply, widthProg_length, length_unary] using hs.2
end
end MIPRE.QLD.PauliAnswerProgram

namespace MIPRE.QLD.PauliAnswerProgram
noncomputable section
open Cost SAT LowDegree LowDegree.BinaryLinear Introspection.FieldTableProgram
/-- Decoding an answer always has the constructor prescribed by its actual question. -/
theorem decodeBits_format {k m d : ℕ} (E : BinField k) (q : Question E.carrier m) (bs : BitStr) :
    q.fmtOk (decodeBits E m d q.ty bs) = true :=
  decodeRows_format E q _
end
end MIPRE.QLD.PauliAnswerProgram

namespace MIPRE.QLD.PauliAnswerProgram
noncomputable section
open Cost SAT LowDegree LowDegree.BinaryLinear Introspection.FieldTableProgram
/-- Every accepted raw payload for the implemented field re-encodes exactly. -/
theorem answerBits_decodeBits (k : ℕ) (hk : 1 ≤ k) (m d : ℕ) (T : Ty) (bs : BitStr)
    (h : (parser (T, unary m, unary k, unary d, bs)).1 = true) :
    answerBits (shoupBinField k hk) (decodeBits (shoupBinField k hk) m d T bs) = bs := by
  obtain ⟨hn, hw, hb⟩ := parser_rows_spec T m k d bs h
  rw [answerBits, decodeBits,
    answerRows_decodeRows (shoupBinField k hk) (shoupBinField_toBits_ofBits k hk) T _ hn hw]
  exact hb
end
end MIPRE.QLD.PauliAnswerProgram

namespace MIPRE.QLD.PauliBooleanProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT PauliCL PauliAnswerProgram
/-- Acceptance forces the exact answer format at both original endpoints,
regardless of which orientation the arithmetic router uses. -/
theorem program_formats (input : Input) (h : program input = true) :
    (parser (input.2.1.1, input.1.2.2, input.1.1, unary 1, input.2.1.2.2)).1 = true ∧
    (parser (input.2.2.1, input.1.2.2, input.1.1, unary 1, input.2.2.2.2)).1 = true := by
  rw [program_apply, Bool.and_eq_true, Bool.and_eq_true] at h
  have hp := h.1
  cases ho : (route input).2.1 <;>
    simp only [leftParser, rightParser, left, right, oriented,
      leftBits, rightBits, dim, width, params, endpoints,
      comp_apply, pair_apply, fst_apply, snd_apply, const_apply,
      ho] at hp
  · exact hp
  · exact hp.symm
end
end MIPRE.QLD.PauliBooleanProgram

namespace MIPRE.QLD.PauliBooleanProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT PauliCL PauliAnswerProgram
set_option backward.isDefEq.respectTransparency false in
theorem program_raw_correct_valid (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (T U : Ty)
    (x y : Coord (2 ^ j) → (shoupBinField k hk).carrier) (a b : BitStr)
    (ha : (parser (T, unary (2 ^ j), unary k, unary 1, a)).1 = true)
    (hb : (parser (U, unary (2 ^ j), unary k, unary 1, b)).1 = true) :
    program ((unary k, unary j, unary (2 ^ j)),
      (T, fieldEncoding (shoupBinField k hk) x, a),
      (U, fieldEncoding (shoupBinField k hk) y, b)) =
      accepts hm (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T x)
        (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) U y)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 T a)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 U b) := by
  have hfa := decodeBits_format (d := 1) (shoupBinField k hk)
    (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T x) a
  have hfb := decodeBits_format (d := 1) (shoupBinField k hk)
    (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) U y) b
  simp only [explicitDecode_ty] at hfa hfb
  have he := program_correct_formatted k hk j hj hm T U x y
    (decodeBits (shoupBinField k hk) (2 ^ j) 1 T a)
    (decodeBits (shoupBinField k hk) (2 ^ j) 1 U b) hfa hfb
  simpa only [encodedInput, answerBits_decodeBits k hk _ _ T a ha,
    answerBits_decodeBits k hk _ _ U b hb] using he
end
end MIPRE.QLD.PauliBooleanProgram

namespace MIPRE.QLD.PauliBooleanProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT PauliCL PauliAnswerProgram
/-- The whole raw predicate: exact parsing followed by the QLD predicate on
the uniquely decoded semantic answers. Malformed payloads are rejected. -/
theorem program_raw_iff (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (T U : Ty)
    (x y : Coord (2 ^ j) → (shoupBinField k hk).carrier) (a b : BitStr) :
    program ((unary k, unary j, unary (2 ^ j)),
      (T, fieldEncoding (shoupBinField k hk) x, a),
      (U, fieldEncoding (shoupBinField k hk) y, b)) = true ↔
      (parser (T, unary (2 ^ j), unary k, unary 1, a)).1 = true ∧
      (parser (U, unary (2 ^ j), unary k, unary 1, b)).1 = true ∧
      accepts hm (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T x)
        (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) U y)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 T a)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 U b) = true := by
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := program_formats _ h
    exact ⟨ha, hb, (program_raw_correct_valid k hk j hj hm T U x y a b ha hb).symm.trans h⟩
  · rintro ⟨ha, hb, h⟩
    exact (program_raw_correct_valid k hk j hj hm T U x y a b ha hb).trans h
end
end MIPRE.QLD.PauliBooleanProgram

namespace MIPRE.QLD.PauliFullAnswerProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryLinear Introspection.FieldTableProgram Introspection.FieldAnswerParser Introspection.BinaryBlock
theorem registerVector_apply {F : Type*} [Field F] [Algebra (ZMod 2) F] {m k : ℕ}
    (b : Module.Basis (Fin k) (ZMod 2) F) (h : (Fin m → Bool) → F)
    (i : Fin (2 ^ m)) (j : Fin k) :
    registerVector b h (finProdFinEquiv (i, j)) =
      b.equivFun (h ((cubeEnumeration m).symm i)) j := by
  simp [registerVector, registerNumbering]
end
end MIPRE.QLD.PauliFullAnswerProgram

namespace MIPRE.QLD.PauliFullAnswerProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryLinear Introspection.FieldTableProgram Introspection.FieldAnswerParser Introspection.BinaryBlock
theorem registerVector_bits {F : Type*} [Field F] [Algebra (ZMod 2) F] {m k : ℕ}
    (b : Module.Basis (Fin k) (ZMod 2) F) (h : (Fin m → Bool) → F) :
    CL.toBits (registerVector b h) =
      (List.ofFn fun i : Fin (2 ^ m) =>
        vectorBits (b.equivFun (h ((cubeEnumeration m).symm i)))).flatten := by
  unfold CL.toBits vectorBits
  rw [CL.ofFn_eq_flatten_blocks]
  simp only [registerVector_apply]
  rfl
end
end MIPRE.QLD.PauliFullAnswerProgram

namespace MIPRE.QLD.PauliFullAnswerProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryLinear Introspection.FieldTableProgram Introspection.FieldAnswerParser Introspection.BinaryBlock
theorem program_answerBits (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (m d : ℕ) (h : (Fin m → Bool) → (shoupBinField k hk).carrier) :
    program (unary m, unary k,
      PauliAnswerProgram.answerBits (shoupBinField k hk) (.pauliAns (d := d) h)) =
      (true, CL.toBits (registerVector (shoupSelfDualNormalBasis k hk hodd) h)) := by
  simp only [program, pair_apply, comp_apply, fst_apply, snd_apply,
    PauliAnswerProgram.answerBits, PauliAnswerProgram.answerRows,
    fullPauliParserProg_vecBits _ hk, encodeBlocksProg_correct k hk hodd,
    registerVector_bits]
end
end MIPRE.QLD.PauliFullAnswerProgram

namespace MIPRE.QLD.PauliFullAnswerProgram
noncomputable section
open Cost SAT PauliAnswerProgram Introspection.FieldTableProgram
theorem decodeBits_pauli {k : ℕ} (E : BinField k) (m : ℕ) (W : Bas) (bs : BitStr) :
    decodeBits E m 1 (.pauli W) bs = .pauliAns (decodedOutcome E m W bs) := rfl
end
end MIPRE.QLD.PauliFullAnswerProgram

namespace MIPRE.QLD.PauliFullAnswerProgram
noncomputable section
open Cost SAT PauliAnswerProgram Introspection.FieldTableProgram
theorem program_raw (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (m : ℕ) (W : Bas) (bs : BitStr)
    (hvalid : (parser (.pauli W, unary m, unary k, unary 1, bs)).1 = true) :
    program (unary m, unary k, bs) =
      (true, CL.toBits (registerVector (shoupSelfDualNormalBasis k hk hodd)
        (decodedOutcome (shoupBinField k hk) m W bs))) := by
  have he := program_answerBits k hk hodd m 1 (decodedOutcome (shoupBinField k hk) m W bs)
  rw [← decodeBits_pauli, answerBits_decodeBits k hk m 1 (.pauli W) bs hvalid] at he
  exact he
end
end MIPRE.QLD.PauliFullAnswerProgram

namespace MIPRE.QLD.PauliBinaryProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT PauliCL PauliAnswerProgram Introspection.PauliStageProgram
theorem endpointValid_apply (k j m : Unary) (T : Ty) (q a : BitStr) :
    endpointValid ((k, j, m), T, q, a) = (parser (T, m, k, unary 1, a)).1 := rfl
end
end MIPRE.QLD.PauliBinaryProgram

namespace MIPRE.QLD.PauliBinaryProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT PauliCL PauliAnswerProgram Introspection.PauliStageProgram
theorem fullAnswer_apply (k j m : Unary) (a : BitStr) :
    fullAnswer ((k, j, m), a) = PauliFullAnswerProgram.program (m, k, a) := rfl
end
end MIPRE.QLD.PauliBinaryProgram

namespace MIPRE.QLD.PauliBinaryProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT PauliCL PauliAnswerProgram Introspection.PauliStageProgram
/-- On every full-length question payload, the actual raw program is exactly
the QLD acceptance relation after the proved basis and answer decoders. -/
theorem program_ofBits_iff (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j : ℕ) (hj : j ≤ k) (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier)
    (T U : Ty) (q r a b : BitStr)
    (hq : q.length = (3 * 2 ^ j + 3) * k)
    (hr : r.length = (3 * 2 ^ j + 3) * k) :
    program ((unary k, unary j, unary (2 ^ j)), (T, q, a), (U, r, b)) = true ↔
      endpointValid ((unary k, unary j, unary (2 ^ j)), T, q, a) = true ∧
      endpointValid ((unary k, unary j, unary (2 ^ j)), U, r, b) = true ∧
      accepts hm (questionOfBits k hk hodd j T q) (questionOfBits k hk hodd j U r)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 T a)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 U b) = true := by
  simp only [program, comp_apply, booleanInput, endpointProg, pair_apply,
    fst_apply, snd_apply, fieldsProg_ofBits k hk hodd _ _ q hq,
    fieldsProg_ofBits k hk hodd _ _ r hr, endpointValid_apply, questionOfBits]
  exact PauliBooleanProgram.program_raw_iff k hk j hj hm T U _ _ a b
end
end MIPRE.QLD.PauliBinaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
open SourceCompiler (GuardInput inputQ inputR inputLeft inputRight leftParts rightParts readInput)
theorem andCheck_iff {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) (x : α) :
    andCheck f g x = true ↔ f x = true ∧ g x = true := by
  simp only [andCheck, PolyTimeFun.ite_apply, const_apply]
  cases f x <;> simp
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram
theorem canonical_encode (M : DecisionPreparation.Metadata) (clock : Unary) (N Q R : ℕ)
    (p : PauliSamplerParameters.Parameters) (n : ℕ) (T U : Label) (x y a b : BitStr) :
    canonical (encode (n,T,x,U,y,a,b),M,clock,N,p,Q,R) = true := by
  simp [canonical, raw, readFields_encode, equal_iff]
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear AuxiliaryProgram
theorem dimension_correct (U : ClockedUniversalMachine) (ctx : AuxiliarySource.Context) (s : ℕ)
    (h : clockedResult (AuxiliarySource.source ctx)
      (encode (AuxiliarySource.index ctx, CL.Sampler.Query.dimension))
      (AuxiliarySource.budget ctx).length = .cons (encode true) (encode s)) :
    dimension U ctx = s := by
  simp only [dimension, comp_apply, pair_apply, const_apply, encoded_apply, ClockedQuery.run_apply]
  rw [h, treeTail_cons, readNat_encode]
end
end MIPRE.Introspection.SourcePadding.Program

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost LowDegree.BinaryLinear AuxiliaryProgram
theorem queryContext_dimension (U : ClockedUniversalMachine) {ℓ lam n : ℕ}
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (w : Bool) (j : ℕ) {Q : ℕ} (u : Fin Q → CL.𝔽₂) :
    dimension U (queryContext V lam n w j u) = V.sampler.dim (2 ^ n) := by
  apply dimension_correct
  simpa only [queryContext, AuxiliarySource.source, AuxiliarySource.index,
    AuxiliarySource.budget, Cost.PolyTimeFun.comp_apply, Cost.PolyTimeFun.fst_apply,
    Cost.PolyTimeFun.snd_apply, length_unary, SourceCompiler.dimensionResult] using
      SourceCompiler.bounded_dimensionResult V hV hn
end
end MIPRE.Introspection.SourcePadding.Program

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem questionDimension_apply (z : Input) :
    questionDimension z = (3 * (parameters z).2.2.length + 3) * (parameters z).1.length := by
  have he := QLD.PauliBinaryProgram.coordinateCount_apply
    (parameters z).1 (parameters z).2.1 (parameters z).2.2
  simp only [questionDimension, ap₂_apply, comp_apply, pair_apply, fst_apply, const_apply,
    LowDegree.DegreeArithmetic.mulUnaryProg_apply, addUnary_apply, length_unary, Nat.zero_add]
  rw [he, length_unary]
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem zeroPrefix_apply (z : Input) :
    zeroPrefix z = List.replicate (min (registerWidth z) ((leftBits z).length + (rightBits z).length))
      false := by
  simp only [zeroPrefix, comp_apply, map_apply, pair_apply, ap₂_apply, append_apply,
    DynamicParser.takeBits_apply]
  change (((leftBits z) ++ (rightBits z)).take (registerWidth z)).map
    (fun _ : Bool => false) = _
  have he (l : List Bool) : l.map (fun _ => false) = List.replicate l.length false := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      simpa only [List.map_cons, List.length_cons, List.replicate_succ] using
        (congrArg (List.cons false) ih)
  rw [he, List.length_take, List.length_append]
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem zeroPrefix_of_length (z : Input)
    (h : registerWidth z ≤ (leftBits z).length + (rightBits z).length) :
    zeroPrefix z = List.replicate (registerWidth z) false := by
  rw [zeroPrefix_apply, Nat.min_eq_left h]
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem program_iff (U : ClockedUniversalMachine) (z : Input) :
    program U z = true ↔ canonical z = true ∧ questionLengths z = true ∧
      leftPauliFormat z = true ∧ rightPauliFormat z = true ∧
      pauli z = true ∧ auxiliary U z = true := by
  simp only [program, andCheck_iff]
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem auxiliaryInput_apply (U : ClockedUniversalMachine) (z : Input) :
    auxiliaryInput U z =
      ((sourceContext z,
        ((registerWidth z, originalCutoff z, sourceDimension U z, sourceDecider z), parameters z)),
        (leftType z, leftBits z), (rightType z, rightBits z)) := rfl
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem sourceContext_apply (z : Input) :
    sourceContext z = (budget z, sourceSampler z, sourceIndex z, false, 1, zeroPrefix z) := rfl
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
set_option maxRecDepth 4096 in
theorem pauli_apply (z : Input) :
    pauli z = if andCheck leftIsPauli rightIsPauli z then
      QLD.PauliBinaryProgram.program
        (parameters z, leftPauliPayload z, rightPauliPayload z) else true := rfl
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun SourcePadding.Program
set_option backward.isDefEq.respectTransparency false
theorem canonicalInput_fields (V : Verifier 7) (lam n Q R : ℕ)
    (p : PauliSamplerParameters.Parameters) (T U : Label) (x y a b : BitStr) :
    leftType (canonicalInput V lam n Q R p T U x y a b) = T ∧
      rightType (canonicalInput V lam n Q R p T U x y a b) = U ∧
      leftBits (canonicalInput V lam n Q R p T U x y a b) = a ∧
      rightBits (canonicalInput V lam n Q R p T U x y a b) = b := by
  simp only [canonicalInput, leftType, rightType, leftBits, rightBits, raw, comp_apply,
    fst_apply, leftLabelField_encode, rightLabelField_encode,
    leftAnswerField_encode, rightAnswerField_encode, and_self]
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun SourcePadding.Program
set_option backward.isDefEq.respectTransparency false
theorem sourceContext_canonical (V : Verifier 7) (lam n Q R : ℕ)
    (p : PauliSamplerParameters.Parameters) (T U : Label) (x y a b : BitStr)
    (hab : Q ≤ a.length + b.length) :
    sourceContext (canonicalInput V lam n Q R p T U x y a b) =
      queryContext V lam n false 0 (0 : Fin Q → CL.𝔽₂) := by
  have hz := zeroPrefix_of_length (canonicalInput V lam n Q R p T U x y a b)
    (by simpa only [canonicalInput_fields, registerWidth, resourceTail, canonicalInput,
      comp_apply, fst_apply, snd_apply, leftBits, rightBits, raw,
      leftAnswerField_encode, rightAnswerField_encode] using hab)
  rw [sourceContext_apply,hz]
  simp only [budget, sourceSampler, sourceIndex, resourceTail, metadata, registerWidth,
    canonicalInput, comp_apply, fst_apply, snd_apply, queryContext,
    CL.Detyping.toBits_zero, Nat.zero_add]
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun SourcePadding.Program
set_option backward.isDefEq.respectTransparency false
theorem auxiliaryInput_canonical (W : ClockedUniversalMachine) {lam n : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n) (Q R : ℕ)
    (p : PauliSamplerParameters.Parameters) (T U : Label) (x y a b : BitStr)
    (hab : Q ≤ a.length + b.length) :
    auxiliaryInput W (canonicalInput V lam n Q R p T U x y a b) =
      AuxiliaryDecision.canonical V lam n Q R p T U a b := by
  have hc := sourceContext_canonical V lam n Q R p T U x y a b hab
  have hd : sourceDimension W (canonicalInput V lam n Q R p T U x y a b) =
      V.sampler.dim (2 ^ n) := by
    rw [sourceDimension, comp_apply, hc]
    exact queryContext_dimension W V hV hn false 0 0
  rw [auxiliaryInput_apply,hc,hd]
  simp only [AuxiliaryDecision.canonical, registerWidth, originalCutoff, sourceDecider,
    metadata, parameters, resourceTail, canonicalInput, leftType, rightType, leftBits,
    rightBits, raw, comp_apply, fst_apply, snd_apply, leftLabelField_encode,
    rightLabelField_encode, leftAnswerField_encode, rightAnswerField_encode]
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryProgram SAT
set_option backward.isDefEq.respectTransparency false
variable (V : Verifier 7) (lam n Q R : ℕ) (p : PauliSamplerParameters.Parameters)
  (T U : Label) (x y a b : BitStr)
theorem canonical_canonicalInput :
    canonical (canonicalInput V lam n Q R p T U x y a b) = true :=
  canonical_encode _ _ _ _ _ _ _ _ _ _ _ _ _
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryProgram SAT
set_option backward.isDefEq.respectTransparency false
variable (V : Verifier 7) (lam n Q R : ℕ) (p : PauliSamplerParameters.Parameters)
  (T U : Label) (x y a b : BitStr)
theorem questionLengths_canonicalInput :
    questionLengths (canonicalInput V lam n Q R p T U x y a b) = true ↔
      x.length = (3 * p.2.2.length + 3) * p.1.length ∧
      y.length = (3 * p.2.2.length + 3) * p.1.length := by
  rw [questionLengths, andCheck_iff]
  simp only [equal_iff, comp_apply, CL.Detyping.DeciderProgram.lengthNat_apply,
    questionDimension_apply, parameters, resourceTail, canonicalInput, fst_apply,
    snd_apply, leftQuestion, rightQuestion, raw, leftQuestionField_encode,
    rightQuestionField_encode]
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryProgram SAT
set_option backward.isDefEq.respectTransparency false
variable (V : Verifier 7) (lam n Q R : ℕ) (p : PauliSamplerParameters.Parameters)
  (T U : Label) (x y a b : BitStr)
theorem leftPauliFormat_canonicalInput (t : QLD.Ty) :
    leftPauliFormat (canonicalInput V lam n Q R p (.inl t) U x y a b) =
      QLD.PauliBinaryProgram.endpointValid (p,t,x,a) := by
  simp only [leftPauliFormat, PolyTimeFun.ite_apply, leftIsPauli, comp_apply,
    finiteFunction_apply, leftType, raw, canonicalInput, fst_apply, leftLabelField_encode,
    isPauli, ↓reduceIte, pair_apply, leftPauliPayload, pauliLabel, leftQuestion,
    leftQuestionField_encode, leftBits, leftAnswerField_encode,
    parameters, resourceTail, snd_apply]
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryProgram SAT
set_option backward.isDefEq.respectTransparency false
variable (V : Verifier 7) (lam n Q R : ℕ) (p : PauliSamplerParameters.Parameters)
  (T U : Label) (x y a b : BitStr)
theorem rightPauliFormat_canonicalInput (u : QLD.Ty) :
    rightPauliFormat (canonicalInput V lam n Q R p T (.inl u) x y a b) =
      QLD.PauliBinaryProgram.endpointValid (p,u,y,b) := by
  simp only [rightPauliFormat, PolyTimeFun.ite_apply, rightIsPauli, comp_apply,
    finiteFunction_apply, rightType, raw, canonicalInput, fst_apply, rightLabelField_encode,
    isPauli, ↓reduceIte, pair_apply, rightPauliPayload, pauliLabel, rightQuestion,
    rightQuestionField_encode, rightBits, rightAnswerField_encode,
    parameters, resourceTail, snd_apply]
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryProgram SAT
set_option backward.isDefEq.respectTransparency false
variable (V : Verifier 7) (lam n Q R : ℕ) (p : PauliSamplerParameters.Parameters)
  (T U : Label) (x y a b : BitStr)
theorem pauli_canonicalInput (t u : QLD.Ty) :
    pauli (canonicalInput V lam n Q R p (.inl t) (.inl u) x y a b) =
      QLD.PauliBinaryProgram.program (p,(t,x,a),(u,y,b)) := by
  rw [pauli_apply]
  simp only [andCheck, PolyTimeFun.ite_apply, leftIsPauli, rightIsPauli, comp_apply,
    finiteFunction_apply, leftType, rightType, raw, canonicalInput, fst_apply,
    leftLabelField_encode, rightLabelField_encode, isPauli, ↓reduceIte,
    leftPauliPayload, rightPauliPayload, pair_apply, pauliLabel, leftQuestion,
    rightQuestion, leftQuestionField_encode, rightQuestionField_encode, leftBits,
    rightBits, leftAnswerField_encode, rightAnswerField_encode, parameters, resourceTail,
    snd_apply]
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryProgram SAT
set_option backward.isDefEq.respectTransparency false
variable (V : Verifier 7) (lam n Q R : ℕ) (p : PauliSamplerParameters.Parameters)
  (T U : Label) (x y a b : BitStr)
omit p T U in
/-- Every actual Pauli-pair computation agrees with QLD on the decoded raw bytes. -/
theorem program_pauli_iff (W : ClockedUniversalMachine)
    (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (t u : QLD.Ty)
    (hx : x.length = (3 * 2 ^ j + 3) * k)
    (hy : y.length = (3 * 2 ^ j + 3) * k) :
    let p : PauliSamplerParameters.Parameters := (unary k,unary j,unary (2 ^ j))
    program W (canonicalInput V lam n Q R p (.inl t) (.inl u) x y a b) = true ↔
      QLD.PauliBinaryProgram.endpointValid (p,t,x,a) = true ∧
      QLD.PauliBinaryProgram.endpointValid (p,u,y,b) = true ∧
      QLD.accepts hm (QLD.PauliBinaryProgram.questionOfBits k hk hodd j t x)
        (QLD.PauliBinaryProgram.questionOfBits k hk hodd j u y)
        (QLD.PauliAnswerProgram.decodeBits (shoupBinField k hk) (2 ^ j) 1 t a)
        (QLD.PauliAnswerProgram.decodeBits (shoupBinField k hk) (2 ^ j) 1 u b) = true ∧
      auxiliary W (canonicalInput V lam n Q R p (.inl t) (.inl u) x y a b) = true := by
  dsimp only
  rw [program_iff, canonical_canonicalInput, questionLengths_canonicalInput,
    leftPauliFormat_canonicalInput, rightPauliFormat_canonicalInput, pauli_canonicalInput,
    QLD.PauliBinaryProgram.program_ofBits_iff k hk hodd j hj hm t u x y a b hx hy]
  simp only [length_unary, hx, hy, true_and]
  tauto
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryProgram SAT
set_option backward.isDefEq.respectTransparency false
variable (V : Verifier 7) (lam n Q R : ℕ) (p : PauliSamplerParameters.Parameters)
  (T U : Label) (x y a b : BitStr)
omit p T U x y in
/-- The callback uses the same explicit full-register numbering as the semantic Pauli outcome. -/
theorem project_canonicalInput (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j m : ℕ) (W : QLD.Bas) (u : Label)
    (ha : (QLD.PauliAnswerProgram.parser (.pauli W,unary m,unary k,unary 1,a)).1 = true) :
    project (AuxiliaryDecision.canonical V lam n Q R (unary k,unary j,unary m)
      (.inl (.pauli W)) u a b) =
      CL.toBits (QLD.PauliFullAnswerProgram.registerVector (shoupSelfDualNormalBasis k hk hodd)
        (QLD.PauliFullAnswerProgram.decodedOutcome (shoupBinField k hk) m W a)) := by
  change (QLD.PauliBinaryProgram.fullAnswer ((unary k,unary j,unary m),a)).2 = _
  rw [QLD.PauliBinaryProgram.fullAnswer_apply,
    QLD.PauliFullAnswerProgram.program_raw k hk hodd m W a ha]
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.AuxiliaryAnswer
section
open Cost
variable {P PA V : Type*} {Q ℓ : ℕ}
/-- Every accepted auxiliary payload already contains one full register. -/
theorem valid_aux_length (R : ℕ) (t : AuxType ℓ) (w : Bool) (bs : BitStr)
    (h : Valid Q R (.inr (t,w) : QuestionType P ℓ) bs) : Q ≤ bs.length := by
  cases t with
  | introspect | sample =>
    rw [h.1, AnswerParser.pairBits_length]
    have hw := h.2.1
    omega
  | read | hide k =>
    rw [h.1, AnswerParser.tripleBits_length]
    have hw := h.2.1
    omega
end
end MIPRE.Introspection.AuxiliaryAnswer

namespace MIPRE.Introspection.DecisionKernel.Answer
noncomputable section
open Cost SAT
set_option backward.isDefEq.respectTransparency false
theorem rawProject_pauliDecode (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j m : ℕ) (W : QLD.Bas) (a : BitStr)
    (ha : (QLD.PauliAnswerProgram.parser (.pauli W,unary m,unary k,unary 1,a)).1 = true) :
    rawProject (unary k,unary j,unary m) (2 ^ m * k) a =
      pauliProject (shoupSelfDualNormalBasis k hk hodd)
        (pauliDecode (shoupBinField k hk) m (.inl (.pauli W)) a) := by
  rw [rawProject, QLD.PauliBinaryProgram.fullAnswer_apply,
    QLD.PauliFullAnswerProgram.program_raw k hk hodd m W a ha]
  simp only [CL.ofBits_toBits, pauliDecode, pauliLabel,
    QLD.PauliFullAnswerProgram.decodeBits_pauli, pauliProject]
end
end MIPRE.Introspection.DecisionKernel.Answer

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost SAT
set_option backward.isDefEq.respectTransparency false
theorem program_leftPauli_valid (W : ClockedUniversalMachine) (V : Verifier 7)
    (lam n Q R : ℕ) (p : PauliSamplerParameters.Parameters) (T : QLD.Ty) (U : Label)
    (x y a b : BitStr)
    (h : program W (canonicalInput V lam n Q R p (.inl T) U x y a b) = true) :
    QLD.PauliBinaryProgram.endpointValid (p,T,x,a) = true := by
  have hf := ((program_iff W _).mp h).2.2.1
  rwa [leftPauliFormat_canonicalInput] at hf
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost SAT
set_option backward.isDefEq.respectTransparency false
theorem program_rightPauli_valid (W : ClockedUniversalMachine) (V : Verifier 7)
    (lam n Q R : ℕ) (p : PauliSamplerParameters.Parameters) (T : Label) (U : QLD.Ty)
    (x y a b : BitStr)
    (h : program W (canonicalInput V lam n Q R p T (.inl U) x y a b) = true) :
    QLD.PauliBinaryProgram.endpointValid (p,U,y,b) = true := by
  have hf := ((program_iff W _).mp h).2.2.2.1
  rwa [rightPauliFormat_canonicalInput] at hf
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun SAT AuxiliaryAnswer
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
theorem program_auxiliary_check (W : ClockedUniversalMachine) {lam n : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n) (Q R : ℕ)
    (p : PauliSamplerParameters.Parameters) (T U : Label) (x y a b : BitStr)
    (hab : Q ≤ a.length + b.length)
    (h : program W (canonicalInput V lam n Q R p T U x y a b) = true) :
    AuxiliaryDecision.check W (.pauli .X) (.pauli .Z) project
      (AuxiliaryDecision.canonical V lam n Q R p T U a b) = true := by
  have hh := ((program_iff W (canonicalInput V lam n Q R p T U x y a b)).mp h).2.2.2.2.2
  simp only [auxiliary, comp_apply] at hh
  rw [auxiliaryInput_canonical W V hV hn Q R p T U x y a b hab] at hh
  exact ((AuxiliaryDecision.guarded_iff (P := QLD.Ty) W (.pauli .X) (.pauli .Z) project
    (AuxiliaryDecision.canonical V lam n Q R p T U a b)).mp hh).2.2
end
end MIPRE.Introspection.DecisionKernel

namespace MIPRE.Introspection.DecisionKernel
noncomputable section
open Cost Cost.PolyTimeFun SAT AuxiliaryAnswer
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
theorem project_rawProject_canonical (V : Verifier 7) (lam n R : ℕ)
    (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j m : ℕ)
    (W : QLD.Bas) (U : Label) (a b : BitStr)
    (ha : (QLD.PauliAnswerProgram.parser (.pauli W,unary m,unary k,unary 1,a)).1 = true) :
    project (AuxiliaryDecision.canonical V lam n (2 ^ m * k) R
      (unary k,unary j,unary m) (.inl (.pauli W)) U a b) =
      CL.toBits (Answer.rawProject (unary k,unary j,unary m) (2 ^ m * k) a) := by
  rw [project_canonicalInput V lam n (2 ^ m * k) R a b k hk hodd j m W U ha,
    Answer.rawProject_pauliDecode k hk hodd j m W a ha]
  rfl
end
end MIPRE.Introspection.DecisionKernel

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.DecisionKernel
open Cost Cost.PolyTimeFun SAT AuxiliaryAnswer
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
theorem _root_.solution (W : ClockedUniversalMachine) {lam n : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier)
    (hs : V.sampler.dim (2 ^ n) ≤ 2 ^ (2 ^ j) * k)
    (hQ : 4 ≤ 2 ^ (2 ^ j) * k) (hR : 3 * ((2 ^ n)^lam) ≤ 2 ^ (2 ^ j) * k)
    (T U : Label) (x y a b : BitStr)
    (h : program W (canonicalInput V lam n (2 ^ (2 ^ j) * k) ((2 ^ n)^lam)
      (unary k,unary j,unary (2 ^ j)) T U x y a b) = true) :
    AuxiliaryQuotient.check (AuxiliaryDecision.padded V hs) (.pauli .X) (.pauli .Z)
      (Answer.rawProject (unary k,unary j,unary (2 ^ j)) (2 ^ (2 ^ j) * k))
      (AuxiliaryDecision.sourcePredicate V hs) (rawPauliCheck k hk hodd j hm x y) T U
      (decode (2 ^ (2 ^ j) * k) T a) (decode (2 ^ (2 ^ j) * k) U b) = true := by
  let p : PauliSamplerParameters.Parameters := (unary k,unary j,unary (2 ^ j))
  let Q := 2 ^ (2 ^ j) * k
  let R := (2 ^ n)^lam
  change program W (canonicalInput V lam n Q R p T U x y a b) = true at h
  have hf := program_auxiliary_facts W V lam n Q R p T U x y a b h
  have hlen := ((program_iff W _).mp h).2.1
  rw [questionLengths_canonicalInput] at hlen
  simp only [p,length_unary] at hlen
  have hDP : ∀ t u, T = .inl t → U = .inl u →
      rawPauliCheck k hk hodd j hm x y t u a b = true := by
    intro t u ht hu
    subst T U
    exact ((program_pauli_iff V lam n Q R x y a b W k hk hodd j hj hm t u
      hlen.1 hlen.2).mp h).2.2.1
  have hpa : ∀ t, (t = QLD.Ty.pauli .X ∨ t = .pauli .Z) → T = .inl t →
      project (AuxiliaryDecision.canonical V lam n Q R p T U a b) =
        CL.toBits (Answer.rawProject p Q a) := by
    intro t ht hT
    subst T
    have hv := program_leftPauli_valid W V lam n Q R p t U x y a b h
    rcases ht with rfl | rfl
    all_goals exact project_rawProject_canonical V lam n R k hk hodd j (2 ^ j) _ U a b hv
  have hpb : ∀ u, (u = QLD.Ty.pauli .X ∨ u = .pauli .Z) → U = .inl u →
      project (AuxiliaryDecision.canonical V lam n Q R p U T b a) =
        CL.toBits (Answer.rawProject p Q b) := by
    intro u hu hU
    subst U
    have hv := program_rightPauli_valid W V lam n Q R p T u x y a b h
    rcases hu with rfl | rfl
    all_goals exact project_rawProject_canonical V lam n R k hk hodd j (2 ^ j) _ T b a hv
  have hcap (hab : Q ≤ a.length + b.length) :
      AuxiliaryQuotient.check (AuxiliaryDecision.padded V hs) (.pauli .X) (.pauli .Z)
        (Answer.rawProject p Q) (AuxiliaryDecision.sourcePredicate V hs)
        (rawPauliCheck k hk hodd j hm x y) T U (decode Q T a) (decode Q U b) = true :=
    AuxiliaryDecision.check_raw_sound (P := QLD.Ty) W (.pauli .X) (.pauli .Z) project V hV hn hs hQ hR
      (Answer.rawProject p Q) (rawPauliCheck k hk hodd j hm x y) T U a b hpa hpb hDP
      (program_auxiliary_check W V hV hn Q R p T U x y a b hab h)
  rcases T with t | ⟨t,w⟩
  · rcases U with u | ⟨u,v⟩
    · have hd := hDP t u rfl rfl
      simp only [AuxiliaryAnswer.decode, AuxiliaryQuotient.check, TypedPredicate.fits,
        AuxiliaryQuotient.directed, Bool.and_true, Bool.true_and]
      by_cases htu : t = u
      · subst u
        have hab := hf.2.2 rfl
        subst b
        simpa using hd
      · simp [htu, hd]
    · exact hcap (by have := valid_aux_length R u v b hf.2.1; omega)
  · exact hcap (by have := valid_aux_length R t w a hf.1; omega)
end MIPRE.Introspection.DecisionKernel

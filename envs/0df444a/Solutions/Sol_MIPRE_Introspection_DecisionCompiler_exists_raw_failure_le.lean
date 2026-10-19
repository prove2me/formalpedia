-- Prove2me | solution 1 for MIPRE.Introspection.DecisionCompiler.exists_raw_failure_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T07:54:10.59455+00:00
-- url     : https://prove2.me/submissions/91a64b37-2d46-4f37-b959-31fccf7eaea2

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/AmbientRawGame.lean (solution of MIPRE.Introspection.DecisionCompiler.exists_raw_failure_le);
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
import Definitions.Def_MIPRE_Foundations_CL_DetypingDecider
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingCompleteSupport
import Definitions.Def_MIPRE_Foundations_CL_DetypingComplete
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderTransport
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
import Definitions.Def_MIPRE_Foundations_Introspection_DecisionPreparationCost
import Definitions.Def_MIPRE_Background_Introspection_DecisionCompilerCutoff
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
import Definitions.Def_MIPRE_Background_Introspection_DecisionCompilerRoute
import Definitions.Def_MIPRE_Background_Introspection_DecisionCompilerZero
import Definitions.Def_MIPRE_Foundations_Introspection_SourceDescriptionCompiler
import Definitions.Def_MIPRE_Background_Introspection_DecisionCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_PauliFactorProg
import Definitions.Def_MIPRE_Background_QLD_SamplerQueryProgram
import Definitions.Def_MIPRE_Background_QLD_PauliFactorPrograms
import Definitions.Def_MIPRE_Background_Introspection_PauliSampler
import Definitions.Def_MIPRE_Background_Introspection_PauliSamplerCost
import Definitions.Def_MIPRE_Foundations_Introspection_SamplerProgram
import Definitions.Def_MIPRE_Foundations_Introspection_Sampler
import Definitions.Def_MIPRE_Foundations_Introspection_SamplerCost
import Definitions.Def_MIPRE_Background_Introspection_PauliSamplerExtension
import Definitions.Def_MIPRE_Background_Introspection_PauliSamplerZero
import Definitions.Def_MIPRE_Background_Introspection_PauliSamplerTotal
import Definitions.Def_MIPRE_Background_Introspection_DecisionCompilerVerifier
import Definitions.Def_MIPRE_Foundations_VerifierIndexTransport
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Background_Introspection_AmbientVerifierTransport
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDecisionCorrect
import Definitions.Def_MIPRE_Background_Introspection_DecisionKernelCanonical
import Definitions.Def_MIPRE_Background_Introspection_AmbientRawGame
import Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_numbered_clDist
import Theorems.Thm_MIPRE_CL_Detyping_graphOfBits_take_eq
import Theorems.Thm_MIPRE_CL_Detyping_select_eq_some_iff
import Theorems.Thm_MIPRE_CL_Detyping_sum_valid_questions
import Theorems.Thm_MIPRE_CL_Detyping_valid_average_le
import Theorems.Thm_MIPRE_Introspection_DecisionCompiler_accepts_positive_bounds
import Theorems.Thm_MIPRE_Introspection_DecisionCompiler_accepts_reference
import Theorems.Thm_MIPRE_Introspection_DecisionCompiler_detypingLoss_nonneg
import Theorems.Thm_MIPRE_Introspection_DecisionCompiler_typedDecider_total
import Theorems.Thm_MIPRE_Introspection_PauliSampler_finalSampler_dim_pos
import Theorems.Thm_MIPRE_Introspection_TypeGraph_edges_nonempty
import Theorems.Thm_MIPRE_Introspection_TypeGraph_symmetric
import Theorems.Thm_MIPRE_SampledGame_one_sub_value
import Theorems.Thm_MIPRE_TensorProductStrategy_failAt_nonneg
import Theorems.Thm_MIPRE_quantumValue_eq_of_equiv

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
/-- Relabeling along equivalences with matching distribution and decision predicate
preserves the value. -/
theorem value_relabel {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : TensorProductStrategy G) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
    (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    (S.relabel G' eX eY eA eB).value = S.value := by
  unfold value
  show (∑ x', ∑ y', ∑ a', ∑ b', G'.μ x' y' * (if G'.D x' y' a' b' then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M (eX x') (eA a') ⊗ₖ S.PB.M (eY y') (eB b')) *ᵥ S.ψ)).re) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re
  symm
  refine Fintype.sum_equiv eX.symm _ _ fun x => Fintype.sum_equiv eY.symm _ _ fun y =>
    Fintype.sum_equiv eA.symm _ _ fun a => Fintype.sum_equiv eB.symm _ _ fun b => ?_
  rw [hμ, hD, eX.apply_symm_apply, eY.apply_symm_apply, eA.apply_symm_apply,
    eB.apply_symm_apply]
end
end MIPRE.TensorProductStrategy

namespace MIPRE.CL.Graph
noncomputable section
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- The one-hot half makes the encoding injective, even for an isolated vertex. -/
theorem encode_injective (E : T → T → Prop) [DecidableRel E] :
    Function.Injective (encode E) := by
  intro u v h
  have hh := congrFun h (false, u)
  by_contra huv
  simpa [encode, huv] using hh
end
end MIPRE.CL.Graph

namespace MIPRE.CL.Graph
noncomputable section
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- Encoding an ordered pair is injective. -/
theorem pairSeed_injective (E : T → T → Prop) [DecidableRel E] :
    Function.Injective (pairSeed E) := by
  intro uv uv' h
  apply Prod.ext
  · apply encode_injective E
    funext p
    exact congrFun h (false, p)
  · apply encode_injective E
    funext p
    exact congrFun h (true, p)
end
end MIPRE.CL.Graph

namespace MIPRE.CL.Graph
noncomputable section
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- The rejection event has exactly one seed per ordered edge. -/
theorem card_validSeeds (E : T → T → Prop) [DecidableRel E] :
    (validSeeds E).card = (edges E).card :=
  Finset.card_image_of_injective _ (pairSeed_injective E)
end
end MIPRE.CL.Graph

namespace MIPRE.CL.Graph
noncomputable section
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- The four binary blocks have `16 ^ |T|` seeds. -/
theorem card_seeds : Fintype.card (Coord T → ZMod 2) = 16 ^ Fintype.card T := by
  simp only [Fintype.card_fun, ZMod.card, Coord, Fintype.card_prod, Fintype.card_bool]
  rw [← mul_assoc, pow_mul]
  norm_num
end
end MIPRE.CL.Graph

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- The conditional joint law is the uniform ordered-edge law with a shared uniform seed. -/
theorem conditional_average {ℓ : ℕ}
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (f : (Coord T ι → ZMod 2) → (Coord T ι → ZMod 2) → ℝ) :
    (∑ g ∈ Graph.validSeeds E, ∑ v : ι → ZMod 2,
      f ((presentation E false (P false)).eval (Sum.elim g v))
        ((presentation E true (P true)).eval (Sum.elim g v))) /
      ((Graph.validSeeds E).card * Fintype.card (ι → ZMod 2)) =
    (∑ uv ∈ Graph.edges E, ∑ v : ι → ZMod 2,
      f (Sum.elim (view E false uv.1) ((P false uv.1).eval v))
        (Sum.elim (view E true uv.2) ((P true uv.2).eval v))) /
      ((Graph.edges E).card * Fintype.card (ι → ZMod 2)) := by
  rw [sum_valid_questions E hE P hP hℓ, Graph.card_validSeeds]
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι A B : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype B]
/-- A valid graph view decodes to its type. -/
theorem select_view (E : T → T → Prop) [DecidableRel E] (w : Bool) (u : T) :
    select E w (view E w u) = some u := by
  apply (select_eq_some_iff _ _ _ _).mpr
  constructor
  · funext p
    simp [view]
  · simp [view]
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι A B : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype B]
/-- On an edge, the fixed graph views make the detyped predicate exactly the typed one. -/
theorem accepts_question (E : T → T → Prop) [DecidableRel E]
    (D : Question T ι → Question T ι → A → B → Bool)
    (x y : Question T ι) (h : E x.1 y.1) (a : A) (b : B) :
    accepts E D (question E false x) (question E true y) a b = D x y a b := by
  unfold accepts question
  change (match select E false (view E false x.1), select E true (view E true y.1) with
    | some u, some v =>
      if E u v ∧ view E false x.1 = view E false u ∧ view E true y.1 = view E true v then
        D (u, x.2) (v, y.2) a b else true
    | _, _ => true) = _
  rw [select_view, select_view]
  simp [h]
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι A B : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype B]
/-- The finite game's law is the library's CL distribution of the constructed presentations. -/
theorem game_mu_eq_clDist {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (x y : Coord T ι → ZMod 2) :
    (game E P D).μ x y = clDist (presentation E false (P false)).eval
      (presentation E true (P true)).eval x y := by
  change SampledGame.dist (presentation E false (P false)).eval
    (presentation E true (P true)).eval x y = _
  exact sampled_dist_cl _ _ _ _
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι A B : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype B]
/-- Conditional failure agrees on every edge, with no change of state. -/
theorem restrict_failAt {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (game E P D))
    (x y : Question T ι) (h : E x.1 y.1) :
    (restrict E hne P D S).failAt x y = S.failAt (question E false x) (question E true y) := by
  unfold TensorProductStrategy.failAt TensorProductStrategy.succAt
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change (if D x y a b then (1 : ℝ) else 0) * _ =
    (if accepts E D (question E false x) (question E true y) a b then 1 else 0) * _
  rw [accepts_question E D x y h]
  rfl
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι A B : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype B]
/-- The typed failure is the uniform edge-and-content average of the restricted failures. -/
theorem typed_failure {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (typedGame E hne P D)) :
    1 - S.value =
      (∑ uv ∈ Graph.edges E, ∑ v : ι → ZMod 2,
        S.failAt (uv.1, (P false uv.1).eval v) (uv.2, (P true uv.2).eval v)) /
      ((Graph.edges E).card * Fintype.card (ι → ZMod 2)) := by
  let _ : Nonempty (Edge E) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  refine (SampledGame.one_sub_value (typedQuestion (E := E) P false) (typedQuestion P true) D S).trans ?_
  simp only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul, Fintype.sum_prod_type,
    typedQuestion, Bool.false_eq_true, ↓reduceIte]
  congr 1
  exact Finset.sum_coe_sort (Graph.edges E) (fun uv => ∑ v : ι → ZMod 2,
    S.failAt (uv.1, (P false uv.1).eval v) (uv.2, (P true uv.2).eval v))
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι A B : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype B]
/-- The detyped failure is the uniform average over its independent graph and content seeds. -/
theorem failure {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (game E P D)) :
    1 - S.value =
      (∑ g : Graph.Coord T → ZMod 2, ∑ v : ι → ZMod 2,
        S.failAt ((presentation E false (P false)).eval (Sum.elim g v))
          ((presentation E true (P true)).eval (Sum.elim g v))) /
      ((16 : ℝ) ^ Fintype.card T * Fintype.card (ι → ZMod 2)) := by
  refine (SampledGame.one_sub_value _ _ _ S).trans ?_
  let e := Equiv.sumArrowEquivProdArrow (Graph.Coord T) ι (ZMod 2)
  have hc := Fintype.card_congr e
  rw [hc, Fintype.card_prod, Graph.card_seeds, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  rw [← Fintype.sum_prod_type']
  exact (e.symm.sum_comp (fun z => S.failAt
    ((presentation E false (P false)).eval z) ((presentation E true (P true)).eval z))).symm
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]
theorem push_register (s : ℕ) (x : Coord T (Fin s) → 𝔽₂) :
    push (registerEquiv s).toEmbedding x =
      Fin.append (push graphEquiv.toEmbedding (pull .inl x)) (pull .inr x) := by
  funext i
  obtain ⟨q, rfl⟩ := (registerEquiv (T := T) s).surjective i
  calc _ = x q := push_apply (registerEquiv s).toEmbedding x q
    _ = _ := by
      cases q with
      | inl q =>
        simp only [registerEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
          Sum.map_inl, finSumFinEquiv_apply_left, Fin.append_left]
        exact (push_apply graphEquiv.toEmbedding (pull .inl x) q).symm
      | inr q => simp [registerEquiv, pull]
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]
theorem toBits_append {m n : ℕ} (x : Fin m → 𝔽₂) (y : Fin n → 𝔽₂) :
    toBits (Fin.append x y) = toBits x ++ toBits y := by
  unfold toBits
  rw [← List.ofFn_fin_append]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp
  · intro j; simp
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- Numbering the sum registers is exactly concatenation of their bit strings. -/
theorem toBits_register (s : ℕ) (x : Coord T (Fin s) → 𝔽₂) :
    toBits (push (registerEquiv s).toEmbedding x) =
      graphBits (pull .inl x) ++ toBits (pull .inr x) := by
  rw [push_register, toBits_append]
  rfl
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Cost.PolyTimeFun Program
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
theorem accepts_selected {ι A B : Type*} [Fintype ι] [DecidableEq ι]
    (P : Question T ι → Question T ι → A → B → Bool)
    (x y : Coord T ι → 𝔽₂) (a : A) (b : B) :
    Detyping.accepts E P x y a b =
      match selectedEdge E (pull .inl x) (pull .inl y) with
      | none => true
      | some uv => P (uv.1, pull .inr x) (uv.2, pull .inr y) a b := by
  unfold Detyping.accepts selectedEdge
  cases select E false (pull .inl x) <;> cases select E true (pull .inl y) <;> simp only
  split_ifs <;> rfl
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Cost.PolyTimeFun Program
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
theorem graphOfBits_register (s : ℕ) (x : Coord T (Fin s) → 𝔽₂) :
    graphOfBits (toBits (push (registerEquiv s).toEmbedding x)) = pull .inl x := by
  rw [← graphOfBits_take_eq, toBits_register]
  simp only [← length_graphBits (pull .inl x), List.take_left, graphOfBits_graphBits]
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Cost.PolyTimeFun Program
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
theorem drop_register (s : ℕ) (x : Coord T (Fin s) → 𝔽₂) :
    (toBits (push (registerEquiv s).toEmbedding x)).drop (graphDim T) = toBits (pull .inr x) := by
  rw [toBits_register]
  simp only [← length_graphBits (pull .inl x), List.drop_left]
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Cost.PolyTimeFun Program
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
/-- On the outer answer alphabet, the compiled predicate is exactly the
already-formalized finite detyping predicate, on every pair of questions. -/
theorem bounded_acceptance (hD : D.Total) (n : ℕ)
    (x y : Coord T (Fin (S.dim n)) → 𝔽₂)
    (a b : MIPRE.Verifier.Answers (C.outer n)) :
    @decide ((decider E S D C).Accepts n
      (toBits (push (registerEquiv (S.dim n)).toEmbedding x))
      (toBits (push (registerEquiv (S.dim n)).toEmbedding y)) a.val b.val)
      (Classical.propDecidable _) =
    Detyping.accepts E (typedPredicate S D C n) x y a b := by
  classical
  rw [accepts_selected]
  have h := accepts_iff E S D C hD n
    (toBits (push (registerEquiv (S.dim n)).toEmbedding x))
    (toBits (push (registerEquiv (S.dim n)).toEmbedding y)) a.val b.val
  simp only [length_toBits, graphOfBits_register, drop_register,
    a.property, b.property, true_and] at h
  simp only [h]
  cases selectedEdge E (pull .inl x) (pull .inl y) <;> simp [typedPredicate]
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Cost.PolyTimeFun Program
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
/-- Predicate equality for the actual ambient verifier's finite game. -/
theorem verifier_game_D (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (x y : Coord T (Fin (S.dim n)) → 𝔽₂)
    (a b : MIPRE.Verifier.Answers (C.outer n)) :
    ((verifier E S D C hℓ hD).game n (C.outer n)).D
      (push (registerEquiv (S.dim n)).toEmbedding x)
      (push (registerEquiv (S.dim n)).toEmbedding y) a b =
      Detyping.accepts E (typedPredicate S D C n) x y a b :=
  bounded_acceptance E S D C hD n x y a b
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- Exact identification of the restricted strategy's failure with conditional detyped failure. -/
theorem restrict_failure_eq {A B : Type*} [Fintype A] [Fintype B] {ℓ : ℕ}
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (game E P D)) :
    1 - (restrict E hne P D S).value =
      (∑ g ∈ Graph.validSeeds E, ∑ v : ι → ZMod 2,
        S.failAt ((presentation E false (P false)).eval (Sum.elim g v))
          ((presentation E true (P true)).eval (Sum.elim g v))) /
        ((Graph.validSeeds E).card * Fintype.card (ι → ZMod 2)) := by
  rw [typed_failure, conditional_average E hE P hP hℓ]
  congr 1
  apply Finset.sum_congr rfl
  intro uv huv
  apply Finset.sum_congr rfl
  intro v _
  exact restrict_failAt E hne P D S _ _ (Finset.mem_filter.mp huv).2
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- The finite-game detyping reduction, with the source's explicit soundness factor. -/
theorem restrict_failure_le {A B : Type*} [Fintype A] [Fintype B] {ℓ : ℕ}
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (game E P D)) :
    1 - (restrict E hne P D S).value ≤ (16 : ℝ) ^ Fintype.card T * (1 - S.value) := by
  rw [restrict_failure_eq E hE hne P hP hℓ D S, failure E P D S]
  exact valid_average_le E hne _ (fun _ _ => S.failAt_nonneg _ _)
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Finset
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
/-- The actual ambient game and the finite game have identical question weights. -/
theorem verifier_game_mu (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (x y : Coord T (Fin (S.dim n)) → 𝔽₂) :
    ((verifier E S D C hℓ hD).game n (C.outer n)).μ
      (vectorEquiv (S.dim n) x) (vectorEquiv (S.dim n) y) =
    (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).μ x y := by
  rw [game_mu_eq_clDist]
  exact numbered_clDist E S n x y
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Finset
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
theorem toFinite_value (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : TensorProductStrategy ((verifier E S D C hℓ hD).game n (C.outer n))) :
    (toFinite E S D C hℓ hD n R).value = R.value := by
  apply R.value_relabel _ (vectorEquiv (S.dim n)) (vectorEquiv (S.dim n)) (.refl _) (.refl _)
  · intro x y
    exact (verifier_game_mu E S D C hℓ hD n x y).symm
  · intro x y a b
    exact (verifier_game_D E S D C hℓ hD n x y a b).symm
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Finset
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
/-- The source detyping soundness factor now applies to the actual program-defined game. -/
theorem restrictAmbient_failure_le (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty) (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : TensorProductStrategy ((verifier E S D C hℓ hD).game n (C.outer n))) :
    1 - (restrictAmbient E S D C hne hℓ hD n R).value ≤
      (16 : ℝ) ^ Fintype.card T * (1 - R.value) := by
  have h := Detyping.restrict_failure_le E hE hne (sourceFamily S n)
    (fun w t => S.cl_exactlyOn n (Player.ofBool w) t) hℓ (typedPredicate S D C n)
    (toFinite E S D C hℓ hD n R)
  rw [toFinite_value] at h
  exact h
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.Introspection.ZeroIndexSampler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL
theorem atZero_cl_pos {ℓ n : ℕ} (S : CL.Sampler ℓ) (hn : n ≠ 0) (w : Player) :
    HEq ((atZero S).cl n w) (S.cl n w) := by
  change HEq ((chosen S n).cl n w) (S.cl n w)
  have hc : chosen S n = S := by simp [chosen, hn]
  have he (A B : CL.Sampler ℓ) (h : A = B) : HEq (A.cl n w) (B.cl n w) := by
    subst B
    rfl
  exact he _ _ hc
end
end MIPRE.Introspection.ZeroIndexSampler

namespace MIPRE.Introspection.PauliSampler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL
theorem finalSampler_cl_pos (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ lam n : ℕ)
    (hl : lam ≠ 0) (hn : n ≠ 0) (w : Player) :
    HEq ((finalSampler c hc he ℓ lam).cl n w) ((fullSampler c hc he ℓ lam).cl n w) := by
  have hproj (A B : CL.Sampler 5) (h : A = B) : HEq (A.cl n w) (B.cl n w) := by
    subst B
    rfl
  have hS : finalSampler c hc he ℓ lam =
      ZeroIndexSampler.atZero (fullSampler c hc he ℓ lam) := if_neg hl
  exact (hproj _ _ hS).trans (ZeroIndexSampler.atZero_cl_pos _ hn w)
end
end MIPRE.Introspection.PauliSampler

namespace MIPRE.Verifier
noncomputable section
open CL
theorem toBits_dimensionEquiv {s t : ℕ} (h : s = t) (x : Fin s → 𝔽₂) :
    toBits (dimensionEquiv h x) = toBits x := by
  subst t
  rfl
end
end MIPRE.Verifier

namespace MIPRE.Verifier
noncomputable section
open CL
theorem clDist_dimensionEquiv {s t ℓ : ℕ} (h : s = t)
    (L R : CLFun 𝔽₂ (Fin s) ℓ) (L' R' : CLFun 𝔽₂ (Fin t) ℓ)
    (hL : HEq L L') (hR : HEq R R') (x y : Fin s → 𝔽₂) :
    clDist L'.eval R'.eval (dimensionEquiv h x) (dimensionEquiv h y) =
      clDist L.eval R.eval x y := by
  subst t
  cases eq_of_heq hL
  cases eq_of_heq hR
  rfl
end
end MIPRE.Verifier

namespace MIPRE.Verifier
noncomputable section
open CL
variable {ℓ : ℕ} {V W : Verifier ℓ} {n T : ℕ}
theorem game_mu_dimensionEquiv (h : SamplerAgreement V W n) (x y : V.Questions n) :
    (W.game n T).μ (dimensionEquiv h.dimension x) (dimensionEquiv h.dimension y) =
      (V.game n T).μ x y :=
  clDist_dimensionEquiv h.dimension _ _ _ _ (h.presentation .alice) (h.presentation .bob) x y
end
end MIPRE.Verifier

namespace MIPRE.Verifier
noncomputable section
open CL
variable {ℓ : ℕ} {V W : Verifier ℓ} {n T : ℕ}
theorem game_D_dimensionEquiv (h : SamplerAgreement V W n)
    (hD : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b)
    (x y : V.Questions n) (a b : Answers T) :
    (W.game n T).D (dimensionEquiv h.dimension x) (dimensionEquiv h.dimension y) a b =
      (V.game n T).D x y a b := by
  classical
  change decide (W.decider.Accepts n _ _ _ _) = decide (V.decider.Accepts n _ _ _ _)
  simp only [toBits_dimensionEquiv]
  exact decide_eq_decide.mpr (hD _ _ _ _).symm
end
end MIPRE.Verifier

namespace MIPRE.Verifier
noncomputable section
open CL
variable {ℓ : ℕ} {V W : Verifier ℓ} {n T : ℕ}
/-- Changing programs away from the current index preserves quantum value. -/
theorem valStar_congr_at (h : SamplerAgreement V W n)
    (hD : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.valStar n T = W.valStar n T :=
  quantumValue_eq_of_equiv (W.game n T) (V.game n T)
    (dimensionEquiv h.dimension) (dimensionEquiv h.dimension) (.refl _) (.refl _)
    (fun x y => (game_mu_dimensionEquiv h x y).symm)
    (fun x y a b => (game_D_dimensionEquiv h hD x y a b).symm)
end
end MIPRE.Verifier

namespace MIPRE.Introspection.DecisionCompiler
noncomputable section
open Cost CL CL.Detyping CL.Detyping.Program
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
theorem samplerAgreement_reference (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) {lam n : ℕ}
    (hl : 1 ≤ lam) (hn : 1 ≤ n) :
    Verifier.SamplerAgreement (output c hc he U source lam) (reference c hc he U source lam n) n := by
  refine ⟨?_,fun w => ?_⟩
  · exact PauliSampler.finalSampler_dim_pos c hc he 7 lam n (by omega) (by omega)
  · exact PauliSampler.finalSampler_cl_pos c hc he 7 lam n (by omega) (by omega) w
end
end MIPRE.Introspection.DecisionCompiler

namespace MIPRE.Introspection.DecisionCompiler
noncomputable section
open Cost CL CL.Detyping CL.Detyping.Program
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
theorem valStar_reference (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) {lam n : ℕ}
    (hl : 1 ≤ lam) (hn : 1 ≤ n) (B : ℕ) :
    (output c hc he U source lam).valStar n B = (reference c hc he U source lam n).valStar n B :=
  Verifier.valStar_congr_at (samplerAgreement_reference c hc he U source hl hn)
    (accepts_reference c hc he U source hl hn)
end
end MIPRE.Introspection.DecisionCompiler

namespace MIPRE.Introspection.DecisionCompiler
noncomputable section
open Cost CL CL.Detyping CL.Detyping.Program
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
theorem output_valStar_cutoff (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (source : Prog × Prog) {lam n B : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n)
    (hB : outerBound c lam n ≤ B) :
    (output c hc he U source lam).valStar n B =
      (output c hc he U source lam).valStar n (outerBound c lam n) := by
  apply Verifier.valStar_eq_of_rejects _ hB
  intro x y a b hlong hacc
  have hh := (accepts_positive_bounds c U source.1 source.2 hl hn x y a b hacc).2.2
  change a.length ≤ outerBound c lam n ∧ b.length ≤ outerBound c lam n at hh
  rcases hlong with hlong | hlong <;> omega
end
end MIPRE.Introspection.DecisionCompiler

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.DecisionCompiler
open Cost CL CL.Detyping CL.Detyping.Program
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
theorem _root_.solution (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) {lam n B : ℕ}
    (hl : 1 ≤ lam) (hn : 1 ≤ n) (hB : outerBound c lam n ≤ B)
    (ε : ℝ) (hv : 1-ε < (output c hc he U source lam).valStar n B) :
    ∃ S : TensorProductStrategy (rawGame c hc he U source lam n),
      1-S.value ≤ detypingLoss*ε := by
  rw [output_valStar_cutoff c hc he U source hl hn hB,
    valStar_reference c hc he U source hl hn] at hv
  let G := (reference c hc he U source lam n).game n (outerBound c lam n)
  let : Nonempty (TensorProductStrategy G) :=
    ⟨(SyncStrategy.const G.doubled ⟨[],by simp⟩).toTensorProductStrategy.undouble⟩
  obtain ⟨S,hS⟩ := (lt_ciSup_iff (TensorProductStrategy.bddAbove_range_value
    ((reference c hc he U source lam n).game n (outerBound c lam n)))).mp hv
  let R := DeciderProgram.restrictAmbient graph (extendedSampler c hc he lam)
    (typedDecider c U (SourceDescriptionCompiler.clamp (source,lam)))
    (constantCutoff (outerBound c lam n))
    (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) 7)
    (by decide) (typedDecider_total c U _) n S
  refine ⟨R,?_⟩
  have hr := DeciderProgram.restrictAmbient_failure_le graph (extendedSampler c hc he lam)
    (typedDecider c U (SourceDescriptionCompiler.clamp (source,lam)))
    (constantCutoff (outerBound c lam n))
    (TypeGraph.symmetric QLD.adj (.pauli .X) (.pauli .Z))
    (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) 7)
    (by decide) (typedDecider_total c U _) n S
  exact hr.trans (mul_le_mul_of_nonneg_left (by linarith) detypingLoss_nonneg)
end MIPRE.Introspection.DecisionCompiler

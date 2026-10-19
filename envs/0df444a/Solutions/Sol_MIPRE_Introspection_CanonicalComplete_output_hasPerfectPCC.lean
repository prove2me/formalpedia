-- Prove2me | solution 1 for MIPRE.Introspection.CanonicalComplete.output_hasPerfectPCC
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T08:25:36.155132+00:00
-- url     : https://prove2.me/submissions/adc8918f-692a-49b8-aeba-052a3898f30f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/CanonicalComplete.lean (solution of MIPRE.Introspection.CanonicalComplete.output_hasPerfectPCC);
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
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
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
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Foundations_CL_DetypingCompleteSupport
import Definitions.Def_MIPRE_Foundations_CL_DetypingComplete
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderTransport
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
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
import Definitions.Def_MIPRE_Foundations_Introspection_HonestMagicSquare
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliObservables
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliMeasurements
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCoreGame
import Definitions.Def_MIPRE_Foundations_Introspection_HonestReading
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsed
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsedHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCompleteAux
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliRegister
import Definitions.Def_MIPRE_Foundations_Introspection_HonestSampling
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliGame
import Definitions.Def_MIPRE_Background_Introspection_BinaryMeasurements
import Definitions.Def_MIPRE_Background_Introspection_BinaryAnchors
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRestriction
import Definitions.Def_MIPRE_Background_QLD_CLTransport
import Definitions.Def_MIPRE_Background_Introspection_PauliRestriction
import Definitions.Def_MIPRE_Background_QLD_CLExplicitTransport
import Definitions.Def_MIPRE_Foundations_GameTransportProjection
import Definitions.Def_MIPRE_Background_Introspection_ExplicitGame
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingValue
import Definitions.Def_MIPRE_Background_Introspection_BinarySampled
import Definitions.Def_MIPRE_Background_Introspection_BinaryGame
import Definitions.Def_MIPRE_Foundations_Introspection_TypedQuotientPredicate
import Definitions.Def_MIPRE_Foundations_GameTransportByQuestion
import Definitions.Def_MIPRE_Foundations_Introspection_TypedQuotientGame
import Definitions.Def_MIPRE_Background_Introspection_BinaryQuotientComplete
import Definitions.Def_MIPRE_Foundations_Introspection_SourceReindex
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientReindex
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixGuardGame
import Definitions.Def_MIPRE_Foundations_Introspection_TypedQuotientReindex
import Definitions.Def_MIPRE_Background_Introspection_NumberedComplete
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryAnswerCoding
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDecisionSoundness
import Definitions.Def_MIPRE_Foundations_Introspection_VerifierSourceGame
import Definitions.Def_MIPRE_Background_Introspection_CanonicalGame
import Definitions.Def_MIPRE_Foundations_Introspection_ParsedPauliTransport
import Definitions.Def_MIPRE_Foundations_Introspection_BoundedAnswerCoding
import Definitions.Def_MIPRE_Background_Introspection_DecisionKernelAnswers
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDecisionCompleteness
import Definitions.Def_MIPRE_Background_Introspection_DecisionKernelEncoding
import Definitions.Def_MIPRE_Background_Introspection_DecisionKernelAuxiliary
import Definitions.Def_MIPRE_Background_Introspection_DecisionKernelSoundness
import Definitions.Def_MIPRE_Background_Introspection_DecisionKernelComplete
import Definitions.Def_MIPRE_Foundations_SyncMergeByQuestion
import Definitions.Def_MIPRE_Background_Introspection_CanonicalComplete
import Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_numbered_clDist
import Theorems.Thm_MIPRE_CL_Detyping_complete_commutes_sample
import Theorems.Thm_MIPRE_CL_Detyping_complete_value
import Theorems.Thm_MIPRE_CL_Detyping_graphOfBits_take_eq
import Theorems.Thm_MIPRE_Introspection_CanonicalComplete_exists_raw_perfectPCC
import Theorems.Thm_MIPRE_Introspection_DecisionCompiler_accepts_reference
import Theorems.Thm_MIPRE_Introspection_DecisionCompiler_accepts_zero
import Theorems.Thm_MIPRE_Introspection_DecisionCompiler_typedDecider_total
import Theorems.Thm_MIPRE_Introspection_PauliSampler_finalSampler_dim_pos
import Theorems.Thm_MIPRE_Introspection_PauliSampler_finalSampler_dim_zero
import Theorems.Thm_MIPRE_Introspection_TypeGraph_edges_nonempty
import Theorems.Thm_MIPRE_Introspection_TypeGraph_symmetric
import Theorems.Thm_MIPRE_SyncStrategy_isPCC_relabel
import Theorems.Thm_MIPRE_SyncStrategy_value_relabel
import Theorems.Thm_MIPRE_Verifier_hasPerfectPCC_of_accepts_diagonal
import Theorems.Thm_MIPRE_Verifier_hasPerfectPCC_of_congr_at

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
open Finset Classical Matrix Kronecker
set_option linter.unusedSectionVars false
variable {T ι A : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A]
/-- The completed strategy is PCC on the entire support of the detyped game. -/
theorem complete_isPCC {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (hS : S.IsPCC) (a₀ : A) :
    (complete E hne P D S a₀).IsPCC := by
  rintro ⟨w, x⟩ ⟨w', y⟩ hxy a b
  rw [Game.doubled_μ] at hxy
  split_ifs at hxy with hw
  · rcases hw with ⟨rfl, rfl⟩
    obtain ⟨s, rfl, rfl⟩ := (sample_dist_pos_iff _ _ _ _).mp hxy
    have hs : s = Sum.elim (pull .inl s) (pull .inr s) := by ext p; cases p <;> rfl
    rw [hs]
    exact complete_commutes_sample E hE hne P hP hℓ D S hS a₀ _ _ a b
  · exact False.elim (lt_irrefl 0 hxy)
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical Matrix Kronecker
set_option linter.unusedSectionVars false
variable {T ι A : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A]
/-- Finite-game detyping preserves a perfect PCC witness and its dimension. -/
theorem exists_perfectPCC {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (hS : S.IsPCC) (hval : S.value = 1)
    (a₀ : A) :
    ∃ R : SyncStrategy (game E P D).doubled, R.IsPCC ∧ R.value = 1 ∧ R.d = S.d :=
  ⟨complete E hne P D S a₀, complete_isPCC E hE hne P hP hℓ D S hS a₀,
    complete_value E hE hne P hP hℓ D S hval a₀, rfl⟩
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
theorem doubled_game_mu (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (p q : Bool × (Fin (graphDim T + S.dim n) → 𝔽₂)) :
    ((verifier E S D C hℓ hD).game n (C.outer n)).doubled.μ p q =
      (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).doubled.μ
        (doubledVectorEquiv (S.dim n) p) (doubledVectorEquiv (S.dim n) q) := by
  change (if p.1 = false ∧ q.1 = true then
    ((verifier E S D C hℓ hD).game n (C.outer n)).μ p.2 q.2 else 0) =
    if p.1 = false ∧ q.1 = true then
      (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).μ
        ((vectorEquiv (S.dim n)).symm p.2) ((vectorEquiv (S.dim n)).symm q.2) else 0
  by_cases h : p.1 = false ∧ q.1 = true
  · rw [if_pos h, if_pos h]
    simpa only [Equiv.apply_symm_apply] using
      verifier_game_mu E S D C hℓ hD n ((vectorEquiv (S.dim n)).symm p.2)
        ((vectorEquiv (S.dim n)).symm q.2)
  · rw [if_neg h, if_neg h]
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Finset
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
theorem doubled_game_D (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (p q : Bool × (Fin (graphDim T + S.dim n) → 𝔽₂))
    (a b : MIPRE.Verifier.Answers (C.outer n)) :
    ((verifier E S D C hℓ hD).game n (C.outer n)).doubled.D p q a b =
      (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).doubled.D
        (doubledVectorEquiv (S.dim n) p) (doubledVectorEquiv (S.dim n) q) a b := by
  change (if p.1 = false ∧ q.1 = true then
    ((verifier E S D C hℓ hD).game n (C.outer n)).D p.2 q.2 a b else false) =
    if p.1 = false ∧ q.1 = true then
      (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).D
        ((vectorEquiv (S.dim n)).symm p.2) ((vectorEquiv (S.dim n)).symm q.2) a b else false
  by_cases h : p.1 = false ∧ q.1 = true
  · rw [if_pos h, if_pos h]
    have hd : ((verifier E S D C hℓ hD).game n (C.outer n)).D
        (vectorEquiv (S.dim n) ((vectorEquiv (S.dim n)).symm p.2))
        (vectorEquiv (S.dim n) ((vectorEquiv (S.dim n)).symm q.2)) a b =
        (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).D
          ((vectorEquiv (S.dim n)).symm p.2) ((vectorEquiv (S.dim n)).symm q.2) a b :=
      verifier_game_D E S D C hℓ hD n ((vectorEquiv (S.dim n)).symm p.2)
        ((vectorEquiv (S.dim n)).symm q.2) a b
    simpa only [Equiv.apply_symm_apply] using hd
  · rw [if_neg h, if_neg h]
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Finset
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
theorem fromFiniteSync_value (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : SyncStrategy (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).doubled) :
    (fromFiniteSync E S D C hℓ hD n R).value = R.value :=
  R.value_relabel _ (doubledVectorEquiv (S.dim n)) (.refl _)
    (doubled_game_mu E S D C hℓ hD n) (doubled_game_D E S D C hℓ hD n)
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Finset
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
theorem fromFiniteSync_isPCC (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : SyncStrategy (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).doubled)
    (hR : R.IsPCC) : (fromFiniteSync E S D C hℓ hD n R).IsPCC :=
  SyncStrategy.isPCC_relabel hR _ (doubledVectorEquiv (S.dim n)) (.refl _)
    (doubled_game_mu E S D C hℓ hD n)
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Finset
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
/-- Perfect PCC completeness for the actual program-defined game, on the same
outer answer alphabet with the source typed cutoff included in the premise. -/
theorem exists_ambientPerfectPCC (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty) (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : SyncStrategy (typedGame E hne (sourceFamily S n) (typedPredicate S D C n)).doubled)
    (hR : R.IsPCC) (hval : R.value = 1) :
    ∃ Q : SyncStrategy ((verifier E S D C hℓ hD).game n (C.outer n)).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = R.d := by
  obtain ⟨Q, hQ, hv, hd⟩ := Detyping.exists_perfectPCC E hE hne (sourceFamily S n)
    (fun w t => S.cl_exactlyOn n (Player.ofBool w) t) hℓ (typedPredicate S D C n)
    R hR hval ⟨[], by simp⟩
  exact ⟨fromFiniteSync E S D C hℓ hD n Q,
    fromFiniteSync_isPCC E S D C hℓ hD n Q hQ,
    (fromFiniteSync_value E S D C hℓ hD n Q).trans hv, hd⟩
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Finset
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
/-- Completeness in the ambient verifier API, with the source typed cutoff
already present in the finite typed game on the same outer alphabet. -/
theorem verifier_hasPerfectPCC (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty) (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : SyncStrategy (typedGame E hne (sourceFamily S n) (typedPredicate S D C n)).doubled)
    (hR : R.IsPCC) (hval : R.value = 1) :
    (verifier E S D C hℓ hD).HasPerfectPCC n (C.outer n) := by
  obtain ⟨Q, hQ, hv, _⟩ := exists_ambientPerfectPCC E S D C hE hne hℓ hD n R hR hval
  exact ⟨Q, hQ, hv⟩
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
variable {ℓ : ℕ} {V W : Verifier ℓ} {n T : ℕ}
theorem SamplerAgreement.symm (h : SamplerAgreement V W n) : SamplerAgreement W V n :=
  ⟨h.dimension.symm, fun w => (h.presentation w).symm⟩
end
end MIPRE.Verifier

namespace MIPRE.Verifier
noncomputable section
open CL
variable {ℓ : ℕ} {V W : Verifier ℓ} {n T : ℕ}
theorem hasPerfectPCC_congr_at (h : SamplerAgreement V W n)
    (hD : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.HasPerfectPCC n T ↔ W.HasPerfectPCC n T :=
  ⟨hasPerfectPCC_of_congr_at h hD,
    hasPerfectPCC_of_congr_at h.symm fun x y a b => (hD x y a b).symm⟩
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
theorem hasPerfectPCC_reference (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) {lam n : ℕ}
    (hl : 1 ≤ lam) (hn : 1 ≤ n) (B : ℕ) :
    (output c hc he U source lam).HasPerfectPCC n B ↔
      (reference c hc he U source lam n).HasPerfectPCC n B :=
  Verifier.hasPerfectPCC_congr_at (samplerAgreement_reference c hc he U source hl hn)
    (accepts_reference c hc he U source hl hn)
end
end MIPRE.Introspection.DecisionCompiler

namespace MIPRE.Introspection.DecisionCompiler
noncomputable section
open Cost CL CL.Detyping CL.Detyping.Program
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-- Empty questions admit the constant empty-answer PCC strategy. -/
theorem hasPerfectPCC_zero (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) (lam n B : ℕ)
    (hz : lam = 0 ∨ n = 0) : (output c hc he U source lam).HasPerfectPCC n B := by
  apply Verifier.hasPerfectPCC_of_accepts_diagonal _ ⟨[],Nat.zero_le B⟩
  intro x y
  apply (accepts_zero c U source.1 source.2 lam n hz _ _ [] []).mpr
  have hd : (output c hc he U source lam).sampler.dim n = 0 :=
    PauliSampler.finalSampler_dim_zero c hc he 7 lam n (by rcases hz with h | h <;> simp [h])
  have hx : (toBits x).length = 0 := (length_toBits x).trans hd
  have hy : (toBits y).length = 0 := (length_toBits y).trans hd
  exact ⟨List.length_eq_zero_iff.mp hx,List.length_eq_zero_iff.mp hy,by simp,by simp⟩
end
end MIPRE.Introspection.DecisionCompiler

namespace MIPRE.Introspection.DecisionCompiler
noncomputable section
open Cost CL CL.Detyping CL.Detyping.Program
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
/-- A perfect typed raw-kernel strategy gives completeness of the actual output. -/
theorem output_hasPerfectPCC_of_raw (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) {lam n B : ℕ}
    (hl : 1 ≤ lam) (hn : 1 ≤ n) (hB : outerBound c lam n ≤ B)
    (S : SyncStrategy (rawGame c hc he U source lam n).doubled)
    (hS : S.IsPCC) (hv : S.value = 1) :
    (output c hc he U source lam).HasPerfectPCC n B := by
  apply Verifier.hasPerfectPCC_of_le _ hB
  apply (hasPerfectPCC_reference c hc he U source hl hn _).mpr
  exact DeciderProgram.verifier_hasPerfectPCC graph (extendedSampler c hc he lam)
    (typedDecider c U (SourceDescriptionCompiler.clamp (source,lam)))
    (constantCutoff (outerBound c lam n))
    (TypeGraph.symmetric QLD.adj (.pauli .X) (.pauli .Z))
    (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) 7)
    (by decide) (typedDecider_total c U _) n S hS hv
end
end MIPRE.Introspection.DecisionCompiler

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.CanonicalComplete
open Cost CL CanonicalGame SourceCompiler PauliSamplerParameters DecisionCompiler
open QLD.PauliCL.ExplicitSeed
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
theorem _root_.solution (c : ℕ) (hc : 2 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (C : ℕ) (hcut : ∀ lam n, cutoffAt c lam n ≤ ansBound C lam n)
    (V : Verifier 7) (lam n : ℕ) (hV : V.IsBounded lam)
    (hv : V.HasPerfectPCC (2^n) ((2^n)^lam)) :
    (DecisionCompiler.output c (by omega) he U (V.sampler.prog,V.decider.prog) lam).HasPerfectPCC n
      (ansBound C lam n) := by
  by_cases hn : n = 0
  · exact hasPerfectPCC_zero c (by omega) he U _ lam n _ (Or.inr hn)
  have hl := hV.two_le
  have hn1 : 1 ≤ n := by omega
  obtain ⟨S,hS,hvS⟩ := exists_raw_perfectPCC c hc he U V hV hn1 hv
  apply output_hasPerfectPCC_of_raw c (by omega) he U _ (by omega) hn1 _ S hS hvS
  simpa only [cutoffAt, show ¬(lam = 0 ∨ n = 0) by omega, ↓reduceIte] using hcut lam n
end MIPRE.Introspection.CanonicalComplete

-- Prove2me | solution 1 for MIPRE.Introspection.NumberedComplete.coordinate_exists_perfectPCC_with_format
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T07:05:39.412372+00:00
-- url     : https://prove2.me/submissions/432de30b-8110-4009-b37b-903ebb4a1f2b

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/NumberedComplete.lean (solution of MIPRE.Introspection.NumberedComplete.coordinate_exists_perfectPCC_with_format);
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
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
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
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg_B
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_SAT_PcpFormat
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
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
import Definitions.Def_MIPRE_Background_QLD_BinaryBlocks
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_WeylBinary
import Definitions.Def_MIPRE_Background_QLD_PauliFullAnswerPrograms
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
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
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
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientChecks
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixGuard
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
import Theorems.Thm_MIPRE_CL_CLFun_eval_reindex
import Theorems.Thm_MIPRE_Introspection_AuxiliaryQuotient_hidingNext_of_legacy
import Theorems.Thm_MIPRE_Introspection_BinaryComplete_game_positive_content
import Theorems.Thm_MIPRE_Introspection_BinaryComplete_sampleOp_commute
import Theorems.Thm_MIPRE_Introspection_BinaryComplete_strategy_value
import Theorems.Thm_MIPRE_Introspection_CLChecks_outputPrefix_outputPrefix
import Theorems.Thm_MIPRE_Introspection_ExplicitGame_game_D
import Theorems.Thm_MIPRE_Introspection_Honest_hideRegister_entry_nonzero
import Theorems.Thm_MIPRE_Introspection_Honest_readRegister_entry_nonzero
import Theorems.Thm_MIPRE_QLD_PauliCL_ExplicitSeed_binaryOutputPermutation_presentation
import Theorems.Thm_MIPRE_SyncStrategy_isPCC_relabel
import Theorems.Thm_MIPRE_SyncStrategy_value_le_copy
import Theorems.Thm_MIPRE_SyncStrategy_value_relabel
import Theorems.Thm_MIPRE_aOp_zero
import Theorems.Thm_MIPRE_tracialValue_le_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SyncStrategy
section
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
variable [DecidableEq A]
variable {G : SynchronousGame X A}
/-- The value of a synchronous strategy is at most one. -/
theorem value_le_one (S : SyncStrategy G) : S.value ≤ 1 :=
  tracialValue_le_one G _ S.P
end
end MIPRE.SyncStrategy

attribute [instance] MIPRE.CommutingStrategy.cstarAlgebra

namespace MIPRE.CL
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
theorem proj_proj_of_disjoint {S T : Finset ι} (h : Disjoint S T) (x : ι → F) :
    proj S (proj T x) = 0 := by
  rw [proj_proj, Finset.disjoint_iff_inter_eq_empty.mp h, proj_empty]
end
end MIPRE.CL

namespace MIPRE.CL.RegLinear
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
variable {S T : Finset ι}
theorem proj_apply_of_disjoint (L : RegLinear F S) (h : Disjoint T S) (x : ι → F) :
    proj T (L x) = 0 := by
  rw [← L.proj_apply x, proj_proj_of_disjoint h]
end
end MIPRE.CL.RegLinear

namespace MIPRE.CL.RegLinear
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
variable {S T : Finset ι}
theorem proj_compl_apply [Fintype ι] (L : RegLinear F S) (x : ι → F) : proj Sᶜ (L x) = 0 :=
  L.proj_apply_of_disjoint disjoint_compl_left x
end
end MIPRE.CL.RegLinear

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
/-- **A point differs from its canonical representative by an element of `S`.** For a line ---
`S = span {w}` --- this is the statement that the base point the seeded test reports lies on the
line through the sampled point, which is what lets a line answer be evaluated at the point. -/
theorem sub_canonLin_mem (S : Submodule F (Fin n → F)) (x : Fin n → F) :
    x - canonLin S x ∈ S :=
  Submodule.sub_projection_mem _ x
end
end MIPRE.CL

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem SupportedOn.lift {P : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (h : T' ⊆ T) : (P.lift T').SupportedOn T := by
  induction P generalizing T T' with
  | zero => exact ⟨h, fun _ => trivial⟩
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    exact ⟨hS, fun v => ih v (hnext v) (Finset.sdiff_subset_sdiff h (Finset.Subset.refl S))⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
/-- Item (1) of `lem:cl-kth`: the `k`-th marginal is a `k`-level CL function on the same space. -/
theorem SupportedOn.truncate {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T) (k : ℕ) :
    (P.truncate k).SupportedOn T := by
  induction k generalizing ℓ P T with
  | zero => trivial
  | succ k ih =>
    cases P with
    | zero => exact (ih (supportedOn_zero T)).lift (Finset.empty_subset T)
    | cons S L₁ next =>
      obtain ⟨hS, hnext⟩ := hP
      exact ⟨hS, fun v => ih (hnext v)⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
/-- A presentation on `V_T` takes its values in `V_T`. -/
theorem SupportedOn.proj_eval {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (x : ι → F) : proj T (P.eval x) = P.eval x := by
  induction P generalizing T x with
  | zero => simp
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    simp only [eval_cons, map_add, L₁.proj_apply_of_subset hS]
    rw [← ih _ (hnext _) (proj Sᶜ x), proj_proj_of_subset' Finset.sdiff_subset]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
theorem SupportedOn.proj_eval_of_subset {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (h : T ⊆ U) (x : ι → F) : proj U (P.eval x) = P.eval x := by
  rw [← hP.proj_eval x, proj_proj_of_subset' h, hP.proj_eval]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
theorem SupportedOn.proj_eval_of_disjoint {P : CLFun F ι ℓ} {T U : Finset ι}
    (hP : P.SupportedOn T) (h : Disjoint U T) (x : ι → F) : proj U (P.eval x) = 0 := by
  rw [← hP.proj_eval x, proj_proj_of_disjoint h]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
/-- The two components of the prefix `L_{≤(k+1)}(x) = L₁ x + r` of a presentation
`cons S L₁ next` on `V_T`: `L₁ x` on `V_S`, and `r`, the prefix of the continuation, on
`V_{T \ S}`. -/
theorem SupportedOn.proj_eval_truncate_succ {S : Finset ι} {L₁ : RegLinear F S}
    {next : (ι → F) → CLFun F ι ℓ} {T : Finset ι} (hP : (cons S L₁ next).SupportedOn T)
    (k : ℕ) (x : ι → F) :
    proj S (((cons S L₁ next).truncate (k + 1)).eval x) = L₁ x ∧
      proj Sᶜ (((cons S L₁ next).truncate (k + 1)).eval x) =
        ((next (L₁ x)).truncate k).eval (proj Sᶜ x) := by
  obtain ⟨hS, hnext⟩ := hP
  have hr := (hnext (L₁ x)).truncate k
  have hsub : T \ S ⊆ Sᶜ := fun i hi => by
    simp only [Finset.mem_sdiff] at hi
    simpa using hi.2
  rw [truncate_succ_cons, eval_cons]
  constructor
  · rw [map_add, L₁.proj_apply, hr.proj_eval_of_disjoint Finset.disjoint_sdiff, add_zero]
  · rw [map_add, L₁.proj_compl_apply, zero_add, hr.proj_eval_of_subset hsub]
end
end MIPRE.CL.CLFun

namespace MIPRE.SyncStrategy
section
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] {G : SynchronousGame X A}
theorem value_copy (S : SyncStrategy G) (G' : SynchronousGame X A)
    (hμ : ∀ x y, G'.μ x y = G.μ x y) (hD : ∀ x y a b, G'.D x y a b = G.D x y a b) :
    (S.copy G').value = S.value := by
  rw [value_eq, value_eq]
  show (∑ x, ∑ y, ∑ a, ∑ b, G'.μ x y * (if G'.D x y a b then 1 else 0) *
      ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hμ, hD]
end
end MIPRE.SyncStrategy

namespace MIPRE.SyncStrategy
section
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] {G : SynchronousGame X A}
theorem isPCC_copy {S : SyncStrategy G} (hS : S.IsPCC) (G' : SynchronousGame X A)
    (hμ : ∀ x y, G'.μ x y = G.μ x y) : (S.copy G').IsPCC :=
  fun x y hxy a b => hS x y (by rwa [hμ] at hxy) a b
end
end MIPRE.SyncStrategy

namespace MIPRE.CL
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [DecidableEq ι']
theorem map_sdiff' (e : ι ≃ ι') (S T : Finset ι) :
    T.map e.toEmbedding \ S.map e.toEmbedding = (T \ S).map e.toEmbedding := by
  ext i; simp [Finset.mem_map_equiv]
end
end MIPRE.CL

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [DecidableEq ι']
variable {ℓ : ℕ}
theorem SupportedOn.reindex (e : ι ≃ ι') {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T) :
    (P.reindex e).SupportedOn (T.map e.toEmbedding) := by
  induction P generalizing T with
  | zero => trivial
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    refine ⟨Finset.map_subset_map.mpr hS, fun v => ?_⟩
    rw [map_sdiff']
    exact ih _ (hnext _)
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
theorem compl_product_univ (S : Finset ι) :
    (S ×ˢ (Finset.univ : Finset κ))ᶜ = Sᶜ ×ˢ Finset.univ := by
  ext ⟨i, j⟩; simp
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
/-- `L^↓ = ↓ ∘ L ∘ ↓⁻¹`. -/
theorem eval_downsize (b : Module.Basis κ K F) (P : CLFun F ι ℓ) (x : ι → F) :
    (P.downsize b).eval (downsizeEquiv b x) = downsizeEquiv b (P.eval x) := by
  induction P generalizing x with
  | zero => simp
  | cons S L₁ next ih =>
    rw [downsize_cons, eval_cons, eval_cons, RegLinear.downsize_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, compl_product_univ,
      ← downsizeEquiv_proj, ih, map_add]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable [DecidableEq ι'] [Fintype ι']
variable {ℓ : ℕ}
theorem eval_reindex' (e : ι ≃ ι') (P : CLFun F ι ℓ) (y : ι' → F) :
    (P.reindex e).eval y = reindexEquiv e (P.eval ((reindexEquiv e).symm y)) := by
  conv_lhs => rw [← (reindexEquiv e).apply_symm_apply y]
  rw [eval_reindex]
end
end MIPRE.CL.CLFun

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- Full evaluation produces exactly the seeded question in `QLD.Game`,
including its seed-dependent diagonal direction and canonical base point. -/
theorem questionOfVector_presentation (hm : m ∣ Fintype.card F)
    (t : Ty) (c : Content F m) :
    questionOfVector t ((presentation hm t).eval (contentVector c)) = c.question hm t := by
  cases t <;> (try cases ‹Bas›) <;>
    simp only [questionOfVector, presentation, seedMap, secondMap, finalMap,
      CL.CLFun.eval, CL.RegLinear.zero_apply, CL.RegLinear.id_apply,
      pointMap_apply, directionMap_apply, Pi.add_apply, Pi.zero_apply,
      vectorContent, Content.question, Content.pt, Content.omega,
      LIDT.CL.rep]
  all_goals
    simp [CL.proj_apply, seedSet, directionSet, finalSet, contentVector]
  all_goals constructor <;> rfl
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t : ℕ} [NeZero m]
/-- Evaluation agrees with the actual field presentation under the binary
coordinate equivalence. -/
theorem binaryPresentation_eval (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (x : Coord m → F) :
    (binaryPresentation hm b T).eval (binaryVectorEquiv b x) =
      binaryVectorEquiv b ((presentation hm T).eval x) := by
  change (((presentation hm T).downsize b).reindex (binaryCoordEquiv m t)).eval
    (CL.reindexEquiv (binaryCoordEquiv m t) (CL.downsizeEquiv b x)) = _
  rw [CL.CLFun.eval_reindex, CL.CLFun.eval_downsize]
  rfl
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t : ℕ} [NeZero m]
theorem binaryQuestion_presentation (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (c : Content F m) :
    binaryQuestion b T ((binaryPresentation hm b T).eval
      (binaryVectorEquiv b (contentVector c))) = c.question hm T := by
  rw [binaryPresentation_eval]
  unfold binaryQuestion
  rw [LinearEquiv.symm_apply_apply, questionOfVector_presentation]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.CL.CLFun
section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- An honest output's first register and remainder recover the two construction branches. -/
theorem SupportedOn.proj_eval_cons {S T : Finset ι} {L : RegLinear F S}
    {next : (ι → F) → CLFun F ι ℓ} (hP : (cons S L next).SupportedOn T) (z : ι → F) :
    proj S ((cons S L next).eval z) = L z ∧
      proj Sᶜ ((cons S L next).eval z) = (next (L z)).eval (proj Sᶜ z) := by
  have h := hP.proj_eval_truncate_succ ℓ z
  simpa only [truncate_self] using h
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The sampling check can compute the honest marginal from the complete claimed output. -/
theorem SupportedOn.outputPrefix_eval {P : CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (z : ι → F) :
    P.outputPrefix k (P.eval z) = (P.truncate k).eval z := by
  induction P generalizing T k z with
  | zero => cases k <;> simp [outputPrefix]
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨hfirst, hrest⟩ := hP.proj_eval_cons z
      rw [outputPrefix_cons, hfirst, hrest, truncate_succ_cons, eval_cons,
        ih _ (hP.2 _) k (proj Sᶜ z)]
end
end MIPRE.CL.CLFun

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hideOp_entry_prefix (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (a : HideLabel F ι) (x x' : ι → F)
    (ha : hideOp P k h a x x' ≠ 0) : (P.truncate k).eval x = a.1 := by
  have he := hideRegister_entry_nonzero P k univ h a
    (univRestriction x) (univRestriction x') ha
  simpa using he
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem coordinateRestrict_proj {U V : Finset ι} (hUV : U ⊆ V) (x : ι → F) :
    coordinateRestrict U (CL.proj V x) = coordinateRestrict U x := by
  ext j
  exact if_pos (hUV ((Fintype.equivFin U).symm j).property)
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false in
/-- The recursive dual answer is exactly the selected coordinate linear
readout, transported back into the original register. -/
theorem dualReadout_stageLinear {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    dualReadout P k y x = coordinateInsert (P.factorOfPrefix k y)
      (CL.lperp (coordinateLinear (stageLinear P k y))
        (coordinateRestrict (P.factorOfPrefix k y) x)) := by
  induction P generalizing T k y x with
  | zero =>
    ext i
    simp [dualReadout, coordinateInsert]
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih _ (hP.2 _) k _ x
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
set_option backward.isDefEq.respectTransparency false
variable {F : Type*} [Field F] {m n : ℕ}
/-- A linear map killing a subspace also kills the part removed by canonical
reduction. This permits changing quotient representatives without identifying
two coordinate enumerations. -/
theorem map_canonLin_of_le_ker {V : Type*} [AddCommGroup V] [Module F V]
    (S : Submodule F (Fin n → F)) (D : (Fin n → F) →ₗ[F] V)
    (hS : S ≤ D.ker) (x : Fin n → F) : D (CL.canonLin S x) = D x := by
  have h := hS (CL.sub_canonLin_mem S x)
  change D (x - CL.canonLin S x) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact h.symm
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {S : Finset ι}
theorem registerDual_idempotent (L : CL.RegLinear F S) (x : ι → F) :
    registerDual L (registerDual L x) = registerDual L x := by
  simp only [registerDual, LinearMap.comp_apply, coordinateRestrict_insert]
  congr 1
  apply map_canonLin_of_le_ker
  rw [CL.ker_lperp]
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset CLChecks
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem registerDual_proj_input {S U : Finset (ι)} (L : CL.RegLinear F S)
    (hSU : S ⊆ U) (x : ι → F) : registerDual L (CL.proj U x) = registerDual L x := by
  simp only [registerDual, LinearMap.comp_apply, coordinateRestrict_proj hSU]
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset CLChecks
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem stageDual_apply {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    stageDual P k y x = dualReadout P k y x := by
  rw [dualReadout_stageLinear hP]
  rfl
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CLChecks AuxiliaryDual
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hidingPauli_of_legacy {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (x : ι → F) (v : RegisterHideAnswer F ι)
    (h : CLChecks.hidingPauli P x v) : hidingPauli P x v := by
  refine ⟨?_, h.2⟩
  have hs : CL.proj (P.factorOfPrefix 0 0) v.2.1 = stageDual P 0 0 x := by
    simpa only [stageDual_apply hP] using h.1
  have hd := congrArg (stageDual P 0 0) hs
  change registerDual (stageLinear P 0 0) (CL.proj (P.factorOfPrefix 0 0) v.2.1) =
    registerDual (stageLinear P 0 0) (registerDual (stageLinear P 0 0) x) at hd
  rw [registerDual_proj_input _ (Subset.refl _), registerDual_idempotent] at hd
  exact hd
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
/-- Every malformed answer has zero effect, for every question. -/
theorem answerOp_format_zero [NeZero m] (hm : m ∣ Fintype.card F) (q : Question F m)
    (a : Answer F m d) (ha : q.fmtOk a = false) : answerOp hm q a = 0 := by
  cases q <;> apply fibre_format_zero <;> try exact ha
  all_goals intro x; rfl
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.PauliCL.ExplicitSeed
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
theorem questionOfVector_outputPermutation (π : F ≃ F) (T : Ty) (x : Coord m → F) :
    questionOfVector T (outputPermutation π T x) = decode π T x := by
  cases T <;> (try cases ‹Bas›) <;> rfl
end
end MIPRE.QLD.PauliCL.ExplicitSeed

namespace MIPRE.QLD.PauliCL.ExplicitSeed
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
variable [Algebra (ZMod 2) F] {t : ℕ}
theorem binaryQuestion_outputPermutation (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (x : Fin ((3*m+3)*t) → ZMod 2) :
    binaryQuestion b T (binaryOutputPermutation π b T x) = binaryDecode π b T x := by
  change questionOfVector T ((binaryVectorEquiv b).symm
    (binaryVectorEquiv b (outputPermutation π T ((binaryVectorEquiv b).symm x)))) = _
  rw [LinearEquiv.symm_apply_apply, questionOfVector_outputPermutation]
  rfl
end
end MIPRE.QLD.PauliCL.ExplicitSeed

namespace MIPRE.Introspection.ExplicitGame
noncomputable section
open Finset Classical
open QLD.PauliCL
open QLD.PauliCL.ExplicitSeed
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
  (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
include hχ in
/-- The raw question equivalence intertwines every sampled typed question. -/
theorem questionEquiv_family (u : QuestionType QLD.Ty ℓ)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    questionEquiv π b (u,(TypedPresentation.family (ExplicitSeed.binaryPresentation χ b) u).eval x) =
      (u,(TypedPresentation.family (QLD.PauliCL.binaryPresentation hm b) u).eval
        (binarySeedPermutation π b x)) := by
  cases u with
  | inl p =>
    exact congrArg (fun y => (Sum.inl p,y))
      (binaryOutputPermutation_presentation hm χ π hχ b p x)
  | inr u => rcases u with ⟨u,w⟩; simp
end
end MIPRE.Introspection.ExplicitGame

namespace MIPRE.Introspection.ExplicitGame
noncomputable section
open Finset Classical
open QLD.PauliCL
open QLD.PauliCL.ExplicitSeed
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
  (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
include hχ in
/-- Equality of the complete typed law, including every auxiliary and mixed edge. -/
theorem game_mu (q r : Question m t ℓ) :
    (game hm χ π b L project D).μ q r =
      (PauliRestriction.fullGame hm b L project D).μ
        (questionEquiv π b q) (questionEquiv π b r) := by
  apply dist_equiv _ _ _ _
    (Equiv.prodCongr (Equiv.refl _) (binarySeedPermutation π b)) (questionEquiv π b)
  · intro s
    exact questionEquiv_family hm χ π hχ b s.1.val.1 s.2
  · intro s
    exact questionEquiv_family hm χ π hχ b s.1.val.2 s.2
end
end MIPRE.Introspection.ExplicitGame

namespace MIPRE.Introspection.ExplicitGame
noncomputable section
open Finset Classical
open QLD.PauliCL
open QLD.PauliCL.ExplicitSeed
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency true
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
  (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
variable [DecidableEq A]
include hχ in
/-- Relabeling the doubled game preserves the PCC property. -/
theorem pccToExplicit_isPCC
    (S : SyncStrategy (PauliRestriction.fullGame hm b L project D).doubled) (hS : S.IsPCC) :
    (pccToExplicit hm χ π b L project D S).IsPCC := by
  apply SyncStrategy.isPCC_relabel hS
  intro q r
  simp only [Game.doubled_μ, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    game_mu hm χ π hχ b L project D]
end
end MIPRE.Introspection.ExplicitGame

namespace MIPRE.Introspection.ExplicitGame
noncomputable section
open Finset Classical
open QLD.PauliCL
open QLD.PauliCL.ExplicitSeed
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency true
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
  (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
variable [DecidableEq A]
include hχ in
/-- Relabeling the doubled game preserves the strategy value. -/
theorem pccToExplicit_value
    (S : SyncStrategy (PauliRestriction.fullGame hm b L project D).doubled) :
    (pccToExplicit hm χ π b L project D S).value = S.value := by
  apply S.value_relabel _ (Equiv.prodCongr (.refl Bool) (questionEquiv π b)) (.refl _)
  · intro q r
    simp only [Game.doubled_μ, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      game_mu hm χ π hχ b L project D]
  · intro q r a a'
    simp only [Game.doubled_D, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      game_D hm χ π b L project D]
end
end MIPRE.Introspection.ExplicitGame

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
variable (R : SyncStrategy (Honest.sourceGame L D).doubled)
theorem op_query (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hL : ∀ w, (L w).SupportedOn univ) (p : QuestionType QLD.Ty ℓ)
    (c : QLD.Content F m) (a : Answer F A m t d) :
    op L D R hm b hL (query hm b p c) a = sampleOp b L D R hm hL c p a := by
  cases p with
  | inl p =>
    change pauliOp b L D R hm (QLD.PauliCL.binaryQuestion b p
      ((QLD.PauliCL.binaryPresentation hm b p).eval _)) a = _
    rw [QLD.PauliCL.binaryQuestion_presentation]
    rfl
  | inr p => rfl
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
variable (R : SyncStrategy (Honest.sourceGame L D).doubled)
theorem op_commute (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F) (hb : LowDegree.IsSelfDualBasis b)
    (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC)
    (q r : Question m t ℓ) (h : 0 < (game (d := d) L D hm b).μ q r)
    (a a' : Answer F A m t d) :
    Commute (op L D R hm b hL q a) (op L D R hm b hL r a') := by
  obtain ⟨c,p,s,he,rfl,rfl⟩ := game_positive_content L D hm b q r h
  rw [op_query, op_query]
  exact sampleOp_commute b L D R hb hm hL hR c p s he a a'
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
variable (R : SyncStrategy (Honest.sourceGame L D).doubled)
set_option backward.isDefEq.respectTransparency false in
theorem strategy_isPCC (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F) (hb : LowDegree.IsSelfDualBasis b)
    (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) :
    (strategy (d := d) L D R hm b hL).IsPCC := by
  intro p q h a a'
  have hh := congrArg (registerOp (Fintype.equivFin (Space L D R)).symm)
    (op_commute L D R hm b hb hL hR p.2 q.2 (doubled_positive L D hm b p q h).2 a a').eq
  simpa only [strategy, registerOp_mul] using hh
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false
variable {PauliType PauliAnswer F A : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F (ι) ℓ) (X Z : PauliType)
  (project : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
/-- Every legacy directed comparison implies the quotient comparison. -/
theorem directed_of_legacy (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (t u : QuestionType PauliType ℓ) (a b : ParsedAnswer (ι → F) A PauliAnswer)
    (h : TypedPredicate.directed L X Z project D t u a b = true) :
    directed L X Z project D t u a b = true := by
  fun_cases directed L X Z project D t u a b <;>
    simp_all only [TypedPredicate.directed, ↓reduceIte, and_self, decide_eq_true_eq]
  · exact hidingNext_of_legacy (hL _) _ _ _ h
  · exact hidingPauli_of_legacy (hL _) _ _ h
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false
variable {PauliType PauliAnswer F A : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F (ι) ℓ) (X Z : PauliType)
  (project : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
/-- Legacy acceptance always implies quotient acceptance, including both orientations. -/
theorem check_of_legacy (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (t u : QuestionType PauliType ℓ) (a b : ParsedAnswer (ι → F) A PauliAnswer)
    (h : TypedPredicate.check L X Z project D DP t u a b = true) :
    check L X Z project D DP t u a b = true := by
  simp only [check, TypedPredicate.check, Bool.and_eq_true] at h ⊢
  refine ⟨⟨⟨h.1.1.1, ?_⟩, directed_of_legacy L X Z project D hL t u a b h.1.2⟩,
    directed_of_legacy L X Z project D hL u t b a h.2⟩
  rcases t with p | ⟨t,w⟩ <;> rcases u with q | ⟨u,v⟩ <;> cases a <;> cases b <;>
    exact h.1.1.2
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.SyncStrategy
noncomputable section
open Matrix Kronecker Finset Classical
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  {G : SynchronousGame X A}
/-- Copying to a relaxed game preserves perfect success. -/
theorem copy_value_eq_one (S : SyncStrategy G) (G' : SynchronousGame X A)
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true)
    (hS : S.value = 1) : (S.copy G').value = 1 :=
  le_antisymm (S.copy G').value_le_one (hS ▸ S.value_le_copy G' hμ hD)
end
end MIPRE.SyncStrategy

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {PauliType PauliAnswer F κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype κ] [DecidableEq κ] [Fintype A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
  (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F (ι) ℓ)
  (project : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
/-- Legacy acceptance implies quotient acceptance on every raw tuple. -/
theorem game_accepts_of_legacy (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (q r : CL.Detyping.Question (QuestionType PauliType ℓ) κ)
    (a b : ParsedAnswer (ι → F) A PauliAnswer)
    (h : (TypedEstimates.parsedGame E X Z P L project D DP).D q r a b = true) :
    (game E X Z P L project D DP).D q r a b = true :=
  check_of_legacy L X Z project D hL _ q.1 r.1 a b h
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {PauliType PauliAnswer F κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype κ] [DecidableEq κ] [Fintype A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
  (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F (ι) ℓ)
  (project : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
variable [DecidableEq A] [DecidableEq PauliAnswer]
/-- Copying an honest strategy keeps its PCC property. -/
theorem copiedPCC_isPCC
    (S : SyncStrategy (TypedEstimates.parsedGame E X Z P L project D DP).doubled)
    (hS : S.IsPCC) : (copiedPCC E X Z P L project D DP S).IsPCC :=
  SyncStrategy.isPCC_copy hS _ (fun _ _ => rfl)
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {PauliType PauliAnswer F κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype κ] [DecidableEq κ] [Fintype A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
  (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F (ι) ℓ)
  (project : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
variable [DecidableEq A] [DecidableEq PauliAnswer]
/-- Every perfect legacy PCC strategy remains perfect in the quotient game. -/
theorem copiedPCC_value_eq_one (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (S : SyncStrategy (TypedEstimates.parsedGame E X Z P L project D DP).doubled)
    (hS : S.value = 1) : (copiedPCC E X Z P L project D DP S).value = 1 := by
  apply S.copy_value_eq_one (game E X Z P L project D DP).doubled (fun _ _ => rfl) _ hS
  intro q r a b h
  simp only [Game.doubled_D] at h ⊢
  split_ifs at h ⊢ with ht
  · exact game_accepts_of_legacy E X Z P L project D DP hL q.2 r.2 a b h
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- A nonzero honest Hide outcome reports an actual output after exactly `k` stages. -/
theorem hideOp_output_attained (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (a : HideLabel F ι) (ha : hideOp P k h a ≠ 0) :
    ∃ x, (P.truncate k).eval x = a.1 := by
  by_contra hn
  apply ha
  ext x x'
  by_contra he
  exact hn ⟨x, hideOp_entry_prefix P k h a x x' he⟩
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- Every earlier prefix of a nonzero honest Hide claim is attained by the same seed. -/
theorem hideOp_prefix_attained (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (a : HideLabel F ι) (ha : hideOp P k h a ≠ 0)
    (j : ℕ) (hj : j ≤ k) : ∃ x, (P.truncate j).eval x = P.outputPrefix j a.1 := by
  obtain ⟨x, hx⟩ := hideOp_output_attained P k h a ha
  refine ⟨x, ?_⟩
  rw [← hx, ← h.outputPrefix_eval k, CLChecks.outputPrefix_outputPrefix h _ hj,
    h.outputPrefix_eval]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- A nonzero honest Read outcome reports an actual complete CL output. -/
theorem readOp_output_attained (P : CL.CLFun F ι ℓ)
    (h : P.SupportedOn univ) (a : ReadLabel F ι) (ha : readOp P h a ≠ 0) :
    ∃ x, P.eval x = a.1 := by
  by_contra hn
  apply ha
  ext x x'
  by_contra he
  have hx := readRegister_entry_nonzero P univ h a
    (univRestriction x) (univRestriction x') he
  exact hn ⟨x, by simpa using hx⟩
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- Every prefix of a nonzero honest Read claim is attained, including `ℓ - 1`. -/
theorem readOp_prefix_attained (P : CL.CLFun F ι ℓ)
    (h : P.SupportedOn univ) (a : ReadLabel F ι) (ha : readOp P h a ≠ 0)
    (j : ℕ) : ∃ x, (P.truncate j).eval x = P.outputPrefix j a.1 := by
  obtain ⟨x, hx⟩ := readOp_output_attained P h a ha
  exact ⟨x, by rw [← hx, h.outputPrefix_eval]⟩
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable {A PA : Type*} [Fintype A] [DecidableEq A] [Fintype PA]
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
/-- Tensoring with the source identity does not create unattained Hide labels. -/
theorem parsedHideOp_prefix_attained (w : Bool) (k : ℕ) (h : (L w).SupportedOn univ)
    (y yp z : ι → F)
    (ha : parsedHideOp (PA := PA) L D R w k h (.hide y yp z) ≠ 0)
    (j : ℕ) (hj : j ≤ k) :
    ∃ x, ((L w).truncate j).eval x = (L w).outputPrefix j y := by
  apply hideOp_prefix_attained (L w) k h (y, yp, z) _ j hj
  intro hz
  apply ha
  simp [parsedHideOp, hz]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable {A PA : Type*} [Fintype A] [DecidableEq A] [Fintype PA]
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
/-- Tensoring with the source answer effect does not create unattained Read labels. -/
theorem parsedReadOp_prefix_attained (w : Bool) (h : (L w).SupportedOn univ)
    (y yp : ι → F) (a : A)
    (ha : parsedReadOp (PA := PA) L D R w h (.read y yp a) ≠ 0) (j : ℕ) :
    ∃ x, ((L w).truncate j).eval x = (L w).outputPrefix j y := by
  apply readOp_prefix_attained (L w) h (y, yp) _ j
  intro hz
  apply ha
  simp [parsedReadOp, fullReadOp, hz]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable {A PA : Type*} [Fintype A] [DecidableEq A] [Fintype PA]
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
/-- Every nonzero honest auxiliary effect passes the local prefix guard. The
claim includes every parsed label, so no format promise is needed. -/
theorem auxOp_nonzero_prefixGuard {P : Type*}
    (hL : ∀ w, (L w).SupportedOn univ) (t : AuxQuestion ℓ)
    (a : ParsedAnswer (ι → F) A PA) (ha : auxOp L D R hL t a ≠ 0) :
    PrefixGuard.holds L (.inr t : QuestionType P ℓ) a := by
  rcases t with ⟨t, w⟩
  cases t <;> cases a <;> try trivial
  · exact parsedReadOp_prefix_attained (PA := PA) L D R w (hL w) _ _ _ ha (ℓ - 1)
  · exact parsedHideOp_prefix_attained (PA := PA) L D R w _ (hL w) _ _ _ ha _ le_rfl
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PA : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype PA] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
theorem coreOp_eq_zero_of_unattained (t : CoreType) (y : ι → F) (a : A)
    (hy : ¬ ∃ x, displayed L t x = y) : coreOp L D R t (y,a) = 0 := by
  have hz : readout (displayed L t) y = 0 := by
    ext x x'
    have hn : displayed L t x ≠ y := fun h => hy ⟨x,h⟩
    simp [readout, Matrix.diagonal_apply, hn]
  simp [coreOp, conditionalReadout, hz]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PA : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype PA] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
theorem coreOp_displayed_attained (t : CoreType) (y : ι → F) (a : A)
    (ha : coreOp L D R t (y,a) ≠ 0) : ∃ x, displayed L t x = y := by
  by_contra hn
  exact ha (coreOp_eq_zero_of_unattained L D R t y a hn)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PA : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype PA] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
/-- A nonzero honest Introspect answer reports an actual full source output. -/
theorem introspectOp_output_attained (w : Bool) (y : ι → F) (a : A)
    (ha : coreOp L D R (false,w) (y,a) ≠ 0) : ∃ x, (L w).eval x = y :=
  coreOp_displayed_attained L D R (false,w) y a ha
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PA : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype PA] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
theorem parsedIntrospectOp_output_attained (w : Bool) (y : ι → F) (a : A)
    (ha : parsedCoreOp (PA := PA) L D R (false,w) (.pair y a) ≠ 0) :
    ∃ x, (L w).eval x = y := introspectOp_output_attained L D R w y a ha
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PA : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype PA] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
theorem auxOp_introspect_output_attained (hL : ∀ w, (L w).SupportedOn univ)
    (w : Bool) (y : ι → F) (a : A)
    (ha : auxOp (PA := PA) L D R hL (.introspect,w) (.pair y a) ≠ 0) :
    ∃ x, (L w).eval x = y := parsedIntrospectOp_output_attained (PA := PA) L D R w y a ha
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (hL : ∀ w, (L w).SupportedOn univ)
theorem strategy_nonzero_prefixGuard (q : Bool × Question m t ℓ)
    (a : Answer F A m t d) (ha : (strategy L D R hm b hL).P.M q a ≠ 0) :
    PrefixGuard.holds L q.2.1 a := by
  have hop : op L D R hm b hL q.2 a ≠ 0 := by
    intro hz
    apply ha
    change registerOp _ (op L D R hm b hL q.2 a) = 0
    rw [hz]
    rfl
  rcases q with ⟨side,q,payload⟩
  cases q with
  | inl p => cases a <;> trivial
  | inr p =>
    apply Honest.auxOp_nonzero_prefixGuard L D R hL p a
    intro hz
    apply hop
    change aOp (HB := Fin 2) (Honest.auxOp L D R hL p a) = 0
    rw [hz, aOp_zero]
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (hL : ∀ w, (L w).SupportedOn univ)
theorem strategy_nonzero_introspect (side w : Bool)
    (payload : Fin ((3*m+3)*t) → ZMod 2) (y : Seed m t) (a : A)
    (ha : (strategy (F := F) (d := d) L D R hm b hL).P.M
      (side, .inr (.introspect,w), payload) (.pair y a) ≠ 0) :
    ∃ x, (L w).eval x = y := by
  apply Honest.auxOp_introspect_output_attained (PA := QLD.Answer F m d) L D R hL w y a
  intro hz
  apply ha
  change registerOp _ (aOp (HB := Fin 2)
    (Honest.auxOp L D R hL (.introspect,w) (.pair y a : Answer F A m t d))) = 0
  rw [hz, aOp_zero]
  rfl
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (hL : ∀ w, (L w).SupportedOn univ)
variable (χ : F → Fin m) (π : F ≃ F)
theorem explicitHonest_prefixGuard (q : Bool × Question m t ℓ)
    (a : Answer F A m t d) (ha : (explicitHonest L D R hm b hL χ π).P.M q a ≠ 0) :
    PrefixGuard.holds L q.2.1 a :=
  strategy_nonzero_prefixGuard L D R hm b hL
    ((Equiv.refl Bool).prodCongr (ExplicitGame.questionEquiv π b) q) a ha
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (hL : ∀ w, (L w).SupportedOn univ)
variable (χ : F → Fin m) (π : F ≃ F)
theorem explicitHonest_introspect (side w : Bool)
    (payload : Fin ((3*m+3)*t) → ZMod 2) (y : Seed m t) (a : A)
    (ha : (explicitHonest (d := d) L D R hm b hL χ π).P.M
      (side, .inr (.introspect,w), payload) (.pair y a) ≠ 0) :
    ∃ x, (L w).eval x = y :=
  strategy_nonzero_introspect L D R hm b hL side w payload y a ha
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (hL : ∀ w, (L w).SupportedOn univ)
variable (χ : F → Fin m) (π : F ≃ F)
theorem quotientHonest_prefixGuard (q : Bool × Question m t ℓ)
    (a : Answer F A m t d) (ha : (quotientHonest L D R hm b hL χ π).P.M q a ≠ 0) :
    PrefixGuard.holds L q.2.1 a := explicitHonest_prefixGuard L D R hm b hL χ π q a ha
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (hL : ∀ w, (L w).SupportedOn univ)
variable (χ : F → Fin m) (π : F ≃ F)
theorem quotientHonest_introspect (side w : Bool)
    (payload : Fin ((3*m+3)*t) → ZMod 2) (y : Seed m t) (a : A)
    (ha : (quotientHonest (d := d) L D R hm b hL χ π).P.M
      (side, .inr (.introspect,w), payload) (.pair y a) ≠ 0) :
    ∃ x, (L w).eval x = y := explicitHonest_introspect L D R hm b hL χ π side w payload y a ha
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (hL : ∀ w, (L w).SupportedOn univ)
variable (χ : F → Fin m) (π : F ≃ F)
theorem quotientHonest_isPCC (hb : LowDegree.IsSelfDualBasis b)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s) (hR : R.IsPCC) :
    (quotientHonest (d := d) L D R hm b hL χ π).IsPCC :=
  AuxiliaryQuotient.copiedPCC_isPCC _ _ _ _ _ _ _ _ _
    (ExplicitGame.pccToExplicit_isPCC hm χ π hχ b L (project b) D _
      (strategy_isPCC L D R hm b hb hL hR))
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (hL : ∀ w, (L w).SupportedOn univ)
variable (χ : F → Fin m) (π : F ≃ F)
theorem quotientHonest_value (hb : LowDegree.IsSelfDualBasis b)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s) (hd : 1 ≤ d)
    (hR : R.IsPCC) (hv : R.value = 1) :
    (quotientHonest (d := d) L D R hm b hL χ π).value = 1 := by
  apply AuxiliaryQuotient.copiedPCC_value_eq_one _ _ _ _ _ _ _ _ hL
  exact (ExplicitGame.pccToExplicit_value hm χ π hχ b L (project b) D _).trans
    (strategy_value L D R hm b hb hd hL hR hv)
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (hL : ∀ w, (L w).SupportedOn univ)
variable (χ : F → Fin m) (π : F ≃ F)
theorem quotientHonest_dimension :
    (quotientHonest (d := d) L D R hm b hL χ π).d =
      2 * Fintype.card (Seed m t) * R.d := by
  change Fintype.card (Space L D R) = _
  simp only [Space, Fintype.card_prod, Fintype.card_fin]
  ring
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (hL : ∀ w, (L w).SupportedOn univ)
theorem strategy_nonzero_pauli_format (side : Bool) (p : QLD.Ty)
    (payload : Fin ((3*m+3)*t) → ZMod 2) (a : QLD.Answer F m d)
    (ha : (strategy L D R hm b hL).P.M (side,.inl p,payload) (.pauli a) ≠ 0) :
    (QLD.PauliCL.binaryQuestion b p payload).fmtOk a = true := by
  by_contra hn
  have hf : (QLD.PauliCL.binaryQuestion b p payload).fmtOk a = false :=
    Bool.eq_false_iff.mpr hn
  apply ha
  change registerOp _ (pauliLift b L D R
    (QLD.Honest.answerOp hm (QLD.PauliCL.binaryQuestion b p payload) a)) = 0
  rw [QLD.Honest.answerOp_format_zero hm _ _ hf, pauliLift_zero]
  rfl
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (hL : ∀ w, (L w).SupportedOn univ)
theorem quotientHonest_pauli_format (χ : F → Fin m) (π : F ≃ F)
    (side : Bool) (p : QLD.Ty) (payload : Fin ((3*m+3)*t) → ZMod 2)
    (a : QLD.Answer F m d)
    (ha : (quotientHonest L D R hm b hL χ π).P.M (side,.inl p,payload) (.pauli a) ≠ 0) :
    (QLD.PauliCL.ExplicitSeed.binaryDecode π b p payload).fmtOk a = true := by
  have h := strategy_nonzero_pauli_format L D R hm b hL side p
    (QLD.PauliCL.ExplicitSeed.binaryOutputPermutation π b p payload) a ha
  rwa [QLD.PauliCL.ExplicitSeed.binaryQuestion_outputPermutation] at h
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.SourceReindex
noncomputable section
open Finset CL Classical
set_option linter.unusedSectionVars false
variable {F ι κ A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ)
  (D : (ι → F) → (ι → F) → A → A → Bool)
theorem game_mu (x y : κ → F) :
    (Honest.sourceGame (family e L) (decider e D)).μ x y =
      (Honest.sourceGame L D).μ ((reindexEquiv e).symm x) ((reindexEquiv e).symm y) := by
  change SampledGame.dist _ _ _ _ = SampledGame.dist _ _ _ _
  unfold SampledGame.dist
  rw [← Fintype.card_congr (reindexEquiv (F := F) e).toEquiv]
  congr 1
  refine Fintype.sum_equiv (reindexEquiv e).symm.toEquiv _ _ fun z => ?_
  simp only [family, CLFun.eval_reindex', Prod.mk.injEq, LinearEquiv.coe_toEquiv]
  simp only [LinearEquiv.eq_symm_apply]
end
end MIPRE.Introspection.SourceReindex

namespace MIPRE.Introspection.SourceReindex
noncomputable section
open Finset CL Classical
set_option linter.unusedSectionVars false
variable {F ι κ A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ)
  (D : (ι → F) → (ι → F) → A → A → Bool)
theorem strategy_isPCC (R : SyncStrategy (Honest.sourceGame L D).doubled) (hR : R.IsPCC) :
    (strategy e L D R).IsPCC := by
  apply SyncStrategy.isPCC_relabel hR
  intro x y
  simp only [Game.doubled_μ, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, game_mu,
    LinearEquiv.coe_toEquiv]
end
end MIPRE.Introspection.SourceReindex

namespace MIPRE.Introspection.SourceReindex
noncomputable section
open Finset CL Classical
set_option linter.unusedSectionVars false
variable {F ι κ A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ)
  (D : (ι → F) → (ι → F) → A → A → Bool)
theorem strategy_value (R : SyncStrategy (Honest.sourceGame L D).doubled) :
    (strategy e L D R).value = R.value := by
  apply R.value_relabel _ ((Equiv.refl Bool).prodCongr (reindexEquiv e).symm.toEquiv) (.refl _)
  · intro x y
    simp only [Game.doubled_μ, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, game_mu,
      LinearEquiv.coe_toEquiv]
  · intro x y a b
    rfl
end
end MIPRE.Introspection.SourceReindex

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.NumberedComplete
open Finset CL Classical BinaryComplete
set_option linter.unusedSectionVars false
variable {F A I : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
  {m t d ℓ : ℕ} [NeZero m]
  (e : I ≃ Coord m t) (L : Bool → CLFun (ZMod 2) I ℓ)
  (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (χ : F → Fin m) (π : F ≃ F)
theorem _root_.solution
    (R : SyncStrategy (Honest.sourceGame L D).doubled)
    (hb : LowDegree.IsSelfDualBasis b) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (hd : 1 ≤ d) (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1) :
    ∃ Q : SyncStrategy (AuxiliaryQuotient.reindexedGame e QLD.adj (.pauli .X) (.pauli .Z)
        (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L (project (d := d) e b) D
        (ExplicitGame.pauliCheck hm π b)).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = 2 * Fintype.card (Seed m t) * R.d ∧
      (∀ q a, Q.P.M q a ≠ 0 →
        PrefixGuard.holds (SourceReindex.family e L) q.2.1 a) ∧
      (∀ side w payload y a,
        Q.P.M (side, .inr (.introspect,w), payload) (.pair y a) ≠ 0 →
        ∃ x, (SourceReindex.family e L w).eval x = y) ∧
      (∀ side p payload a, Q.P.M (side,.inl p,payload) (.pauli a) ≠ 0 →
        (QLD.PauliCL.ExplicitSeed.binaryDecode π b p payload).fmtOk a = true) := by
  let Lc := SourceReindex.family e L
  let Dc := SourceReindex.decider e D
  let Rc := SourceReindex.strategy e L D R
  have hLc : ∀ w, (Lc w).SupportedOn univ := fun w => by
    simpa only [Lc, SourceReindex.family, map_univ_equiv] using (hL w).reindex e
  have hRc : Rc.IsPCC := SourceReindex.strategy_isPCC e L D R hR
  have hvRc : Rc.value = 1 := (SourceReindex.strategy_value e L D R).trans hv
  have hproj : (fun a : QLD.Answer F m d => reindexEquiv e (project e b a)) =
      BinaryComplete.project b := by
    funext a
    exact (reindexEquiv e).apply_symm_apply _
  let Gc := AuxiliaryQuotient.reindexedGame e QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L (project (d := d) e b) D
    (ExplicitGame.pauliCheck hm π b)
  have hgame : Gc = BinaryComplete.explicitQuotientGame Lc Dc hm b χ π := by
    change AuxiliaryQuotient.game _ _ _ _ _ _ _ _ = _
    rw [hproj]
    rfl
  let Q := BinaryComplete.quotientHonest (d := d) Lc Dc Rc hm b hLc χ π
  have hμ : ∀ x y, Gc.doubled.μ x y =
      (BinaryComplete.explicitQuotientGame Lc Dc hm b χ π).doubled.μ x y :=
    fun _ _ => by rw [hgame]
  refine ⟨Q.copy Gc.doubled,
    SyncStrategy.isPCC_copy
      (BinaryComplete.quotientHonest_isPCC Lc Dc Rc hm b hLc χ π hb hχ hRc) _ hμ,
    (Q.value_copy _ hμ (fun _ _ _ _ => by rw [hgame])).trans
      (BinaryComplete.quotientHonest_value Lc Dc Rc hm b hLc χ π hb hχ hd hRc hvRc),
    ?_, BinaryComplete.quotientHonest_prefixGuard Lc Dc Rc hm b hLc χ π,
    BinaryComplete.quotientHonest_introspect Lc Dc Rc hm b hLc χ π,
    BinaryComplete.quotientHonest_pauli_format Lc Dc Rc hm b hLc χ π⟩
  exact BinaryComplete.quotientHonest_dimension (d := d) Lc Dc Rc hm b hLc χ π
end MIPRE.Introspection.NumberedComplete

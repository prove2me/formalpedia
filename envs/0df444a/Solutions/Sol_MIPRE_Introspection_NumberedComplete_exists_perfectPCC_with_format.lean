-- Prove2me | solution 1 for MIPRE.Introspection.NumberedComplete.exists_perfectPCC_with_format
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T07:19:10.860459+00:00
-- url     : https://prove2.me/submissions/0475331a-cc62-40cb-a39d-4e774f12be2d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/NumberedComplete.lean (solution of MIPRE.Introspection.NumberedComplete.exists_perfectPCC_with_format);
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
import Theorems.Thm_MIPRE_CL_CLFun_factorOfPrefix_reindex
import Theorems.Thm_MIPRE_CL_CLFun_truncate_reindex
import Theorems.Thm_MIPRE_Introspection_AuxiliaryQuotient_stageDual_reindex_eq_iff
import Theorems.Thm_MIPRE_Introspection_NumberedComplete_coordinate_exists_perfectPCC_with_format
import Theorems.Thm_MIPRE_SyncStrategy_isPCC_relabel
import Theorems.Thm_MIPRE_SyncStrategy_value_copy_of_nonzero
import Theorems.Thm_MIPRE_SyncStrategy_value_relabel

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset CL
variable {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem map_compl (e : ι ≃ κ) (S : Finset ι) :
    (Sᶜ).map e.toEmbedding = (S.map e.toEmbedding)ᶜ := by
  ext i
  simp only [mem_map_equiv, mem_compl]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset CL
variable {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem outputPrefix_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    (P.reindex e).outputPrefix k (reindexEquiv e y) =
      reindexEquiv e (P.outputPrefix k y) := by
  induction P generalizing k y with
  | zero => cases k <;> simp [CLFun.outputPrefix]
  | cons S L next ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [CLFun.reindex_cons, CLFun.outputPrefix_cons, CLFun.outputPrefix_cons,
        ← map_compl, ← reindexEquiv_proj, ← reindexEquiv_proj,
        LinearEquiv.symm_apply_apply, ih, map_add]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset CL
variable {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem prefixRegister_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    prefixRegister (P.reindex e) k (reindexEquiv e y) =
      (prefixRegister P k y).map e.toEmbedding := by
  induction P generalizing k y with
  | zero => cases k <;> simp [prefixRegister]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      rw [CLFun.reindex_cons]
      simp only [prefixRegister]
      rw [← map_compl, ← reindexEquiv_proj, ← reindexEquiv_proj,
        LinearEquiv.symm_apply_apply, ih, map_union]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks AuxiliaryDual Classical
set_option linter.unusedSectionVars false
variable {F ι κ A PA PT : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem reindex_eq_iff (e : ι ≃ κ) (x y : ι → F) :
    reindexEquiv e x = reindexEquiv e y ↔ x = y := (reindexEquiv e).injective.eq_iff
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks AuxiliaryDual Classical
set_option linter.unusedSectionVars false
variable {F ι κ A PA PT : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem hidingNext_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ) (k : ℕ)
    (y yp x z zp v : ι → F) :
    hidingNext (P.reindex e) k
      (reindexEquiv e y, reindexEquiv e yp, reindexEquiv e x)
      (reindexEquiv e z, reindexEquiv e zp, reindexEquiv e v) ↔
      hidingNext P k (y, yp, x) (z, zp, v) := by
  simp only [hidingNext, outputPrefix_reindex, prefixRegister_reindex,
    ← CLChecks.map_compl, ← reindexEquiv_proj, reindex_eq_iff,
    stageDual_reindex_eq_iff]
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks AuxiliaryDual Classical
set_option linter.unusedSectionVars false
variable {F ι κ A PA PT : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem hidingPauli_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ)
    (x y yp z : ι → F) :
    hidingPauli (P.reindex e) (reindexEquiv e x)
      (reindexEquiv e y, reindexEquiv e yp, reindexEquiv e z) ↔
      hidingPauli P x (y, yp, z) := by
  unfold hidingPauli
  rw [← map_zero (reindexEquiv (F := F) e), stageDual_reindex_eq_iff,
    CLFun.factorOfPrefix_reindex, ← CLChecks.map_compl, ← reindexEquiv_proj,
    ← reindexEquiv_proj, reindex_eq_iff]
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks AuxiliaryDual Classical
set_option linter.unusedSectionVars false
variable {F ι κ A PA PT : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem hidingRead_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ)
    (y yp x z zp : ι → F) (a : A) :
    CLChecks.hidingRead (P.reindex e)
      (reindexEquiv e y, reindexEquiv e yp, reindexEquiv e x)
      (reindexEquiv e z, reindexEquiv e zp, a) ↔
      CLChecks.hidingRead P (y, yp, x) (z, zp, a) := by
  simp only [CLChecks.hidingRead, outputPrefix_reindex, reindex_eq_iff]
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks AuxiliaryDual Classical
set_option linter.unusedSectionVars false
variable {F ι κ A PA PT : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
variable (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ) (X Z : PT)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
set_option backward.isDefEq.respectTransparency false in
theorem directed_reindex (t u : QuestionType PT ℓ)
    (a b : ParsedAnswer (ι → F) A PA) :
    directed (fun w => (L w).reindex e) X Z (fun a => reindexEquiv e (project a))
      (fun x y => D ((reindexEquiv e).symm x) ((reindexEquiv e).symm y))
      t u (answerEquiv e a) (answerEquiv e b) = directed L X Z project D t u a b := by
  fun_cases directed L X Z project D t u a b <;>
    simp_all only [directed, answerEquiv, Equiv.coe_fn_mk, CLChecks.sampling,
      CLFun.eval_reindex, CLChecks.reading, hidingRead_reindex, hidingNext_reindex,
      hidingPauli_reindex, reindex_eq_iff, LinearEquiv.symm_apply_apply,
      and_self, ↓reduceIte] <;> try rfl
  case case3 => exact decide_eq_decide.mpr Iff.rfl
  case case5 => exact decide_eq_decide.mpr Iff.rfl
  case case14 =>
    split <;> try rfl
    all_goals cases a <;> cases b <;> simp_all [-Bool.forall_bool]
    all_goals
      rename_i hbad
      exfalso
      apply hbad <;> rfl
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks AuxiliaryDual Classical
set_option linter.unusedSectionVars false
variable {F ι κ A PA PT : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
variable (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ) (X Z : PT)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
theorem check_reindex (DP : PT → PT → PA → PA → Bool)
    (t u : QuestionType PT ℓ) (a b : ParsedAnswer (ι → F) A PA) :
    check (fun w => (L w).reindex e) X Z (fun a => reindexEquiv e (project a))
      (fun x y => D ((reindexEquiv e).symm x) ((reindexEquiv e).symm y))
      DP t u (answerEquiv e a) (answerEquiv e b) = check L X Z project D DP t u a b := by
  simp only [check, fits_answerEquiv, Equiv.apply_eq_iff_eq, directed_reindex]
  cases t <;> cases u <;> cases a <;> cases b <;> rfl
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.PrefixGuard
noncomputable section
open Classical
set_option linter.unusedSectionVars false
variable {F ι A PA P Q : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype PA] [DecidableEq PA] [Fintype Q] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (type : Q → QuestionType P ℓ)
  (G : Game Q Q (ParsedAnswer (ι → F) A PA) (ParsedAnswer (ι → F) A PA))
/-- Any strategy whose nonzero effects satisfy the guard retains its exact
value, without requiring perfection as an intermediate premise. -/
theorem copied_value (S : SyncStrategy G.doubled)
    (hS : ∀ q a, S.P.M q a ≠ 0 → holds L (type q.2) a) :
    (S.copy (game L type G).doubled).value = S.value := by
  apply S.value_copy_of_nonzero (game L type G).doubled (fun _ _ => rfl)
  intro q r a b ha hb
  have hqa := hS q a ha
  have hrb := hS r b hb
  simp [Game.doubled_D, game, check, hqa, hrb]
end
end MIPRE.Introspection.PrefixGuard

namespace MIPRE.Introspection.PrefixGuard
noncomputable section
open Classical
set_option linter.unusedSectionVars false
variable {F ι A PA P Q : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype PA] [DecidableEq PA] [Fintype Q] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (type : Q → QuestionType P ℓ)
  (G : Game Q Q (ParsedAnswer (ι → F) A PA) (ParsedAnswer (ι → F) A PA))
theorem copied_value_eq_one (S : SyncStrategy G.doubled)
    (hS : ∀ q a, S.P.M q a ≠ 0 → holds L (type q.2) a) (hv : S.value = 1) :
    (S.copy (game L type G).doubled).value = 1 :=
  (copied_value L type G S hS).trans hv
end
end MIPRE.Introspection.PrefixGuard

namespace MIPRE.Introspection.PrefixGuard
noncomputable section
open Classical
set_option linter.unusedSectionVars false
variable {F ι A PA P Q : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype PA] [DecidableEq PA] [Fintype Q] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (type : Q → QuestionType P ℓ)
  (G : Game Q Q (ParsedAnswer (ι → F) A PA) (ParsedAnswer (ι → F) A PA))
theorem copied_isPCC (S : SyncStrategy G.doubled) (hS : S.IsPCC) :
    (S.copy (game L type G).doubled).IsPCC :=
  SyncStrategy.isPCC_copy hS _ (fun _ _ => rfl)
end
end MIPRE.Introspection.PrefixGuard

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {F ι κ A PA PT Q : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem prefix_attained_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    (∃ x, ((P.reindex e).truncate k).eval x =
      (P.reindex e).outputPrefix k (reindexEquiv e y)) ↔
      ∃ x, (P.truncate k).eval x = P.outputPrefix k y := by
  rw [CLFun.truncate_reindex, outputPrefix_reindex]
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨(reindexEquiv e).symm x, ?_⟩
    rw [CLFun.eval_reindex'] at hx
    exact (reindexEquiv e).injective hx
  · rintro ⟨x,hx⟩
    exact ⟨reindexEquiv e x, by rw [CLFun.eval_reindex, hx]⟩
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {F ι κ A PA PT Q : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
theorem prefixGuard_reindex (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ)
    (t : QuestionType PT ℓ) (a : ParsedAnswer (ι → F) A PA) :
    PrefixGuard.holds (fun w => (L w).reindex e) t (answerEquiv e a) ↔
      PrefixGuard.holds L t a := by
  rcases t with p | ⟨t,w⟩
  · cases a <;> rfl
  · cases t <;> cases a <;> try rfl
    all_goals exact prefix_attained_reindex e _ _ _
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {F ι κ A PA PT Q : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PA]
  [Fintype PT] [DecidableEq PT] [Fintype Q] [DecidableEq Q]
  (e : ι ≃ κ) (E : PT → PT → Bool) (X Z : PT)
  (P : PT → CLFun (ZMod 2) Q 3) (L : Bool → CLFun F ι ℓ)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PT → PT → (Q → ZMod 2) → (Q → ZMod 2) → PA → PA → Bool)
theorem reindexedGame_D (q r : CL.Detyping.Question (QuestionType PT ℓ) Q)
    (a b : ParsedAnswer (ι → F) A PA) :
    (reindexedGame e E X Z P L project D DP).D q r (answerEquiv e a) (answerEquiv e b) =
      (game E X Z P L project D DP).D q r a b :=
  check_reindex e L X Z project D _ _ _ _ _
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {F ι κ A PA PT Q : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PA]
  [Fintype PT] [DecidableEq PT] [Fintype Q] [DecidableEq Q]
  (e : ι ≃ κ) (E : PT → PT → Bool) (X Z : PT)
  (P : PT → CLFun (ZMod 2) Q 3) (L : Bool → CLFun F ι ℓ)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PT → PT → (Q → ZMod 2) → (Q → ZMod 2) → PA → PA → Bool)
variable [DecidableEq A] [DecidableEq PA]
theorem originalPCC_isPCC
    (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled) (hS : S.IsPCC) :
    (originalPCC e E X Z P L project D DP S).IsPCC :=
  SyncStrategy.isPCC_relabel hS _ _ _ (fun _ _ => rfl)
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {F ι κ A PA PT Q : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PA]
  [Fintype PT] [DecidableEq PT] [Fintype Q] [DecidableEq Q]
  (e : ι ≃ κ) (E : PT → PT → Bool) (X Z : PT)
  (P : PT → CLFun (ZMod 2) Q 3) (L : Bool → CLFun F ι ℓ)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PT → PT → (Q → ZMod 2) → (Q → ZMod 2) → PA → PA → Bool)
variable [DecidableEq A] [DecidableEq PA]
theorem originalPCC_value
    (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled) :
    (originalPCC e E X Z P L project D DP S).value = S.value := by
  apply S.value_relabel _ (Equiv.refl _) (answerEquiv e) (fun _ _ => rfl)
  intro q r a b
  simp only [Game.doubled_D, Equiv.refl_apply, reindexedGame_D]
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CL CLChecks Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {F ι κ A PA PT Q : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PA]
  [Fintype PT] [DecidableEq PT] [Fintype Q] [DecidableEq Q]
  (e : ι ≃ κ) (E : PT → PT → Bool) (X Z : PT)
  (P : PT → CLFun (ZMod 2) Q 3) (L : Bool → CLFun F ι ℓ)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PT → PT → (Q → ZMod 2) → (Q → ZMod 2) → PA → PA → Bool)
variable [DecidableEq A] [DecidableEq PA]
theorem originalPCC_prefixGuard
    (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled)
    (hS : ∀ q a, S.P.M q a ≠ 0 →
      PrefixGuard.holds (fun w => (L w).reindex e) q.2.1 a)
    (q : Bool × CL.Detyping.Question (QuestionType PT ℓ) Q)
    (a : ParsedAnswer (ι → F) A PA)
    (ha : (originalPCC e E X Z P L project D DP S).P.M q a ≠ 0) :
    PrefixGuard.holds L q.2.1 a :=
  (prefixGuard_reindex e L q.2.1 a).mp (hS q (answerEquiv e a) ha)
end
end MIPRE.Introspection.AuxiliaryQuotient

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
    ∃ Q : SyncStrategy (guardedGame (d := d) e L D hm b χ π).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = 2 * Fintype.card (Seed m t) * R.d ∧
      (∀ q a, Q.P.M q a ≠ 0 → PrefixGuard.holds L q.2.1 a) ∧
      (∀ side w payload y a,
        Q.P.M (side, .inr (.introspect,w), payload) (.pair y a) ≠ 0 →
        ∃ x, (L w).eval x = y) ∧
      (∀ side p payload a, Q.P.M (side,.inl p,payload) (.pauli a) ≠ 0 →
        (QLD.PauliCL.ExplicitSeed.binaryDecode π b p payload).fmtOk a = true) := by
  obtain ⟨Q,hQ,hvQ,hdQ,hguard,hintro,hformat⟩ :=
    coordinate_exists_perfectPCC_with_format e L D hm b χ π R hb hχ hd hL hR hv
  let S := AuxiliaryQuotient.originalPCC e QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L (project (d := d) e b) D
    (ExplicitGame.pauliCheck hm π b) Q
  have hS : S.IsPCC := AuxiliaryQuotient.originalPCC_isPCC _ _ _ _ _ _ _ _ _ Q hQ
  have hvS : S.value = 1 := (AuxiliaryQuotient.originalPCC_value _ _ _ _ _ _ _ _ _ Q).trans hvQ
  have hdS : S.d = 2 * Fintype.card (Seed m t) * R.d :=
    (AuxiliaryQuotient.originalPCC_dimension _ _ _ _ _ _ _ _ _ Q).trans hdQ
  have hguardS : ∀ q a, S.P.M q a ≠ 0 → PrefixGuard.holds L q.2.1 a :=
    AuxiliaryQuotient.originalPCC_prefixGuard _ _ _ _ _ _ _ _ _ Q hguard
  refine ⟨S.copy (guardedGame e L D hm b χ π).doubled,
    PrefixGuard.copied_isPCC L Prod.fst _ S hS,
    PrefixGuard.copied_value_eq_one L Prod.fst _ S hguardS hvS,
    hdS, hguardS, ?_, hformat⟩
  intro side w payload y a ha
  obtain ⟨x,hx⟩ := hintro side w payload (reindexEquiv e y) a ha
  refine ⟨(reindexEquiv e).symm x, ?_⟩
  change ((L w).reindex e).eval x = reindexEquiv e y at hx
  rw [CLFun.eval_reindex'] at hx
  exact (reindexEquiv e).injective hx
end MIPRE.Introspection.NumberedComplete

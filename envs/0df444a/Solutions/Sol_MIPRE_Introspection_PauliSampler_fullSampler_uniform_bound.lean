-- Prove2me | solution 1 for MIPRE.Introspection.PauliSampler.fullSampler_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T07:16:49.117592+00:00
-- url     : https://prove2.me/submissions/6498424f-23c9-453e-9872-db51950920f4

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/PauliSamplerExtension.lean (solution of MIPRE.Introspection.PauliSampler.fullSampler_uniform_bound);
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
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
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
import Definitions.Def_MIPRE_Foundations_GameDouble
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
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg_B
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
import Definitions.Def_MIPRE_Background_QLD_BinaryBlocks
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRowsProg
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_PauliFactorProg
import Definitions.Def_MIPRE_Background_QLD_SamplerQueryProgram
import Definitions.Def_MIPRE_Background_QLD_PauliFactorPrograms
import Definitions.Def_MIPRE_Background_Introspection_PauliSampler
import Definitions.Def_MIPRE_Background_Introspection_PauliSamplerCost
import Definitions.Def_MIPRE_Foundations_Introspection_SamplerProgram
import Definitions.Def_MIPRE_Foundations_Introspection_Sampler
import Definitions.Def_MIPRE_Foundations_Introspection_SamplerCost
import Definitions.Def_MIPRE_Background_Introspection_PauliSamplerExtension
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_CL_Detyping_Program_route_preserves
import Theorems.Thm_MIPRE_Cost_Prog_routeCost_natDegree_le
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_haltsWithin
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_hardcode_wellScoped
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_costMajorant_polyBounded
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_prog_closed
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_prog_runs_cost
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_selectorBits_le_fieldBits
import Theorems.Thm_MIPRE_Introspection_PauliSampler_coefficient_le_majorant
import Theorems.Thm_MIPRE_Introspection_PauliSampler_fullSampler_dim

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.TypedSampler
section
open Cost
variable {ℓ : ℕ} {T : Type*} [SizedEncoding T]
theorem TimeBoundAt.mono {S : TypedSampler ℓ T} {n B k B' k' : ℕ}
    (h : S.TimeBoundAt n B k) (hB : B ≤ B') (hk : k ≤ k') :
    S.TimeBoundAt n B' k' := by
  intro d
  obtain ⟨r, t, ht, hr⟩ := h d
  exact ⟨r, t, ht.trans (Nat.mul_le_mul hB (Nat.pow_le_pow_right (by omega) hk)), hr⟩
end
end MIPRE.CL.TypedSampler

namespace MIPRE.Cost.Prog
section
open PolyTimeFun
theorem callWithContext_closed {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) : (callWithContext p post).WellScoped 1 := by
  refine ⟨fstProg_wellScoped, hp.mono (by omega) _, ?_⟩
  exact ⟨⟨callVar_wellScoped (by decide) sndProg_wellScoped, by simp [WellScoped]⟩,
    post.closed.mono (by omega) _⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open PolyTimeFun Polynomial
theorem callWithContext_cost {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) (a ctx r : Data) (time : ℕ)
    (hr : p.Runs a r time) :
    ∃ t ≤ 2 * a.size + 2 * ctx.size + r.size + time +
        post.timeBound.eval (ctx.size + r.size + 1) + 12,
      (callWithContext p post).Runs (.cons a ctx) (post (ctx, r)) t := by
  obtain ⟨tp, htp, hpRun⟩ := post.computes (ctx, r)
  have ectx := callVar_eval (env := [r, a, Data.cons a ctx]) (i := 2)
    sndProg_wellScoped (by simp) (sndProg_runs a ctx)
  have run := Eval.let_ (fstProg_runs a ctx)
    (Eval.let_ (Eval.append_of_wellScoped hr hp _)
      (Eval.let_ (Eval.cons ectx (Eval.var_of_get (i := 0) (by simp)))
        (Eval.append_of_wellScoped hpRun post.closed _)))
  refine ⟨_, ?_, run⟩
  simp only [esize_prod, esize_data, Data.size_cons, encode_data] at *
  omega
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open PolyTimeFun Polynomial
theorem routeOneCall_indirect_cost (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data)
    (x a ctx r : Data) (time : ℕ) (h : route x = (true, .cons a ctx))
    (hr : p.Runs a r time) :
    ∃ t ≤ route.timeBound.eval x.size + 3 * a.size + 3 * ctx.size + r.size + time +
        post.timeBound.eval (ctx.size + r.size + 1) + 18,
      (routeOneCall route p post).Runs x (post (ctx, r)) t := by
  obtain ⟨t, ht, hroute⟩ := route.computes x
  rw [h] at hroute
  obtain ⟨tc, htc, hc⟩ := callWithContext_cost hp post a ctx r time hr
  refine ⟨_, ?_, Eval.let_ hroute
    (Eval.elim_cons (i := 0) (a := Data.cons .nil .nil) (b := .cons a ctx)
      (by simp [encode, Data.ofBool])
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := .nil) (by simp)
        (callVar_eval (i := 3) (callWithContext_closed hp post) (by simp) hc)))⟩
  simp only [esize_data, Data.size_cons] at *
  omega
end
end MIPRE.Cost.Prog

namespace MIPRE.CL.Detyping
section
open Cost Polynomial
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T] {ℓ : ℕ}
variable (E : T → T → Prop) [DecidableRel E] (S : TypedSampler ℓ T)
theorem samplerCost_natDegree_le (n B k : ℕ) :
    (samplerCost E n B k).natDegree ≤ samplerDegree E k := by
  have hi : (X + C (esize n + 1) : Polynomial ℕ).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (by simp only [natDegree_X]; omega)
      (by simp only [natDegree_C]; omega)
  exact natDegree_comp_le.trans ((Nat.mul_le_mul
    (Prog.routeCost_natDegree_le _ _ B k) hi).trans (by simp [samplerDegree]))
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
section
open Cost Polynomial
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T] {ℓ : ℕ}
variable (E : T → T → Prop) [DecidableRel E] (S : TypedSampler ℓ T)
theorem sampler_haltsWithin (hℓ : 0 < ℓ) (n B k : ℕ) (h : S.TimeBoundAt n B k) (q : Data) :
    HaltsWithin (sampler E S hℓ).prog (.cons (encode n) q)
      ((samplerCost E n B k).eval q.size) := by
  have hr := Prog.routeOneCall_haltsWithin (Program.route E) S.closed
    (Program.post (graphDim T)) n B k q h (Program.route_preserves E n q)
  simpa only [sampler, samplerProg, samplerCost, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, Data.size_cons, esize, encode_data,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hr
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
section
open Cost Polynomial
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T] {ℓ : ℕ}
variable (E : T → T → Prop) [DecidableRel E] (S : TypedSampler ℓ T)
/-- Detyping preserves a polynomial query bound with a degree independent of `n`. -/
theorem sampler_timeBoundAt_uniform_degree (hℓ : 0 < ℓ) (n B k : ℕ)
    (h : S.TimeBoundAt n B k) :
    (sampler E S hℓ).TimeBoundAt n (samplerCoefficient E n B k) (samplerDegree E k) := by
  let Q := samplerCost E n B k
  have hQ : (sampler E S hℓ).TimeBoundAt n (samplerCoefficient E n B k) Q.natDegree := by
    intro q
    obtain ⟨r, time, ht, hr⟩ := sampler_haltsWithin E S hℓ n B k h q
    exact ⟨r, time, ht.trans ((polynomial_eval_mono Q (Nat.le_succ q.size)).trans
      (polynomial_eval_le_sum_coeff_mul_pow Q (by omega))), hr⟩
  exact hQ.mono le_rfl (samplerCost_natDegree_le E n B k)
end
end MIPRE.CL.Detyping

namespace MIPRE.Introspection.PauliSamplerParameters
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler
theorem registerPower_le (c lam n : ℕ) :
    registerPower c lam n ≤ c * canonicalLog lam n + 1 := by
  apply Nat.lt_size.mp
  have h := Nat.size_pos.mpr (show 0 < c * canonicalLog lam n + 1 by omega)
  omega
end
end MIPRE.Introspection.PauliSamplerParameters

namespace MIPRE.Introspection.PauliSamplerParameters
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler
theorem fieldBits_le (c lam n : ℕ) :
    fieldBits c lam n ≤ c * canonicalLog lam n + 1 := by
  have hs : (canonicalLog lam n - 1).size ≤ canonicalLog lam n :=
    (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans (Nat.sub_le _ _)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left c hs) 1
end
end MIPRE.Introspection.PauliSamplerParameters

namespace MIPRE.Introspection.PauliSamplerParameters
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler ClockArithmetic
theorem parameters_le_widthBound {c lam n v : ℕ} (hc : 1 ≤ c) (hu : lam * n ≤ v) :
    fieldBits c lam n ≤ widthBound c v ∧
    selectorBits c lam n ≤ widthBound c v ∧
    registerPower c lam n ≤ widthBound c v := by
  have ht : canonicalLog lam n ≤ v + 2 := by unfold canonicalLog; omega
  have hw : c * canonicalLog lam n + 1 ≤ widthBound c v := by
    unfold widthBound
    gcongr
  have hk := (fieldBits_le c lam n).trans hw
  exact ⟨hk, (selectorBits_le_fieldBits hc lam n).trans hk,
    (registerPower_le c lam n).trans hw⟩
end
end MIPRE.Introspection.PauliSamplerParameters

namespace MIPRE.Introspection.PauliSampler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL CL.Detyping.Program Polynomial
open PauliSamplerParameters
theorem costPolynomial_degree (c lam n : ℕ) :
    (costPolynomial c lam n).natDegree ≤ degree := by
  have hR : route.timeBound.natDegree ≤ degree := le_max_left _ _
  have hP : post.timeBound.natDegree ≤ degree :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hQ : QLD.PauliCL.SamplerProgram.query.timeBound.natDegree ≤ degree :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h1 : 1 ≤ degree :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  unfold costPolynomial
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact natDegree_add_le_of_degree_le ((shifted_degree _ _).trans hR)
          (by simp only [natDegree_C]; exact Nat.zero_le _)
      · exact (natDegree_C_mul_le _ _).trans (by simpa using h1)
    · exact (shifted_degree _ _).trans hP
  · exact (shifted_degree _ _).trans hQ
end
end MIPRE.Introspection.PauliSampler

namespace MIPRE.Introspection.PauliSampler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL CL.Detyping.Program Polynomial
open PauliSamplerParameters
theorem prog_runs_cost (c lam n : ℕ) (d : Data) :
    ∃ time ≤ (costPolynomial c lam n).eval d.size,
      (prog c lam).Runs (.cons (encode n) d)
        (QLD.PauliCL.SamplerProgram.query (parameters c lam n, d)) time := by
  obtain ⟨t₁, ht₁, h₁⟩ := PauliSamplerParameters.prog_runs_cost c lam n
  have h₂ := hardcode_time (PauliSamplerParameters.prog_closed c) h₁
  obtain ⟨t₃, ht₃, h₃⟩ := routeOneCall_indirect_cost route
    (hardcode_wellScoped (PauliSamplerParameters.prog_closed c) _) post
    (.cons (encode n) d) (encode n) d (encode (parameters c lam n)) _
    (by simp [route, readNat_encode]) h₂
  have hout : post (d, encode (parameters c lam n)) =
      encode (parameters c lam n, d) := rfl
  rw [hout] at h₃
  obtain ⟨t₄, ht₄, h₄⟩ := QLD.PauliCL.SamplerProgram.query.computes (parameters c lam n, d)
  refine ⟨_, ?_, Eval.let_ h₃
    (Eval.append_of_wellScoped h₄ QLD.PauliCL.SamplerProgram.query.closed _)⟩
  simp only [costPolynomial, eval_add, eval_mul, eval_C, eval_X, eval_comp]
  simp only [Data.size_cons] at ht₃
  simp only [esize_prod, esize_data] at ht₄
  change t₃ ≤ route.timeBound.eval (esize n + d.size + 1) + 3 * esize n +
    3 * d.size + esize (parameters c lam n) + (t₁ + esize lam + esize n + 3) +
    post.timeBound.eval (d.size + esize (parameters c lam n) + 1) + 18 at ht₃
  have hR : esize n + d.size + 1 = d.size + (esize n + 1) := by omega
  have hP : d.size + esize (parameters c lam n) + 1 =
      d.size + (esize (parameters c lam n) + 1) := by omega
  have hQ : esize (parameters c lam n) + d.size + 1 =
      d.size + (esize (parameters c lam n) + 1) := by omega
  rw [hR, hP] at ht₃
  rw [hQ] at ht₄
  omega
end
end MIPRE.Introspection.PauliSampler

namespace MIPRE.Introspection.PauliSampler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL CL.Detyping.Program Polynomial
open PauliSamplerParameters
theorem sampler_timeBoundAt (c : ℕ) (hc : 1 ≤ c) (he : Even c) (lam n : ℕ) :
    (sampler c hc he lam).TimeBoundAt n (coefficient c lam n) degree := by
  intro d
  obtain ⟨t, ht, hr⟩ := prog_runs_cost c lam n d
  refine ⟨_, t, ht.trans ?_, hr⟩
  apply (polynomial_eval_mono _ (Nat.le_succ d.size)).trans
  apply (polynomial_eval_le_sum_coeff_mul_pow _ (by omega)).trans
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) (costPolynomial_degree c lam n))
end
end MIPRE.Introspection.PauliSampler

namespace MIPRE.Introspection.PauliSampler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL CL.Detyping.Program Polynomial
open PauliSamplerParameters
theorem coefficientMajorant_polyBounded (c : ℕ) : PolyBounded (coefficientMajorant c) := by
  unfold coefficientMajorant widthBound
  repeat' first
    | exact costMajorant_polyBounded c
    | apply PolyBounded.add
    | apply PolyBounded.mul
    | apply PolyBounded.eval
    | apply PolyBounded.const
    | exact PolyBounded.id
end
end MIPRE.Introspection.PauliSampler

namespace MIPRE.Introspection.PauliSampler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL CL.Detyping.Program Polynomial
open PauliSamplerParameters
theorem dimension_le_majorant {c lam n v : ℕ} (hc : 1 ≤ c) (hu : lam * n ≤ v) :
    dimension c lam n ≤ dimensionMajorant c v := by
  obtain ⟨hk, _, hm⟩ := parameters_le_widthBound hc hu
  unfold dimension dimensionMajorant
  gcongr
end
end MIPRE.Introspection.PauliSampler

namespace MIPRE.Introspection.PauliSampler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL CL.Detyping.Program Polynomial
open PauliSamplerParameters
theorem dimensionMajorant_polyBounded (c : ℕ) : PolyBounded (dimensionMajorant c) := by
  unfold dimensionMajorant widthBound
  repeat' first
    | apply PolyBounded.add
    | apply PolyBounded.mul
    | apply PolyBounded.const
    | exact PolyBounded.id
end
end MIPRE.Introspection.PauliSampler

namespace MIPRE.Introspection.SamplerProgram
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program
theorem aux_apply (p : Parsed) : aux p = auxResult p := by
  have hf : (const false : PolyTimeFun Bool Bool).toFun = fun _ => false := rfl
  have ht : (const true : PolyTimeFun Bool Bool).toFun = fun _ => true := rfl
  simp only [aux, auxResult, pKind, pLevel, pU, pY, pad, PolyTimeFun.ite_apply,
    ap₂_apply, SAT.ArrayProg.eqNat_apply, const_apply, comp_apply, map_apply,
    fst_apply, snd_apply, decide_eq_true_eq, hf, ht]
  split_ifs <;> simp_all
end
end MIPRE.Introspection.SamplerProgram

namespace MIPRE.Introspection.SamplerProgram
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program
theorem route_apply (x : Data) : route x = routeResult x := by
  simp only [route, routeResult, PolyTimeFun.ite_apply, comp_apply, pair_apply, const_apply,
    ap₂_apply, treePair_apply, encoded_apply, aux_apply, directResult, callResult,
    rawTruthProg]
end
end MIPRE.Introspection.SamplerProgram

namespace MIPRE.Introspection.SamplerProgram
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program
theorem route_preserves (n : ℕ) (q a : Data)
    (h : route (.cons (encode n) q) = (true, a)) :
    ∃ d ctx, a = .cons (.cons (encode n) d) ctx := by
  rw [route_apply] at h
  simp only [routeResult, treeHead_cons, treeTail_cons] at h
  by_cases hq : rawTruth q = true
  · by_cases ht : rawTruth (treeHead (treeHead q)) = true
    · simp [hq, ht, directResult] at h
    · simp [hq, ht, callResult] at h
      exact ⟨_, .nil, h.symm⟩
  · simp [hq, callResult] at h
    exact ⟨.nil, .nil, h.symm⟩
end
end MIPRE.Introspection.SamplerProgram

namespace MIPRE.Introspection
noncomputable section
open Cost CL Polynomial
theorem typedSamplerCost_natDegree_le (n B k : ℕ) :
    (typedSamplerCost n B k).natDegree ≤ typedSamplerDegree k := by
  have hi : (X + Polynomial.C (esize n + 1) : Polynomial ℕ).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (by simp only [natDegree_X]; omega)
      (by simp only [natDegree_C]; omega)
  exact natDegree_comp_le.trans ((Nat.mul_le_mul
    (Prog.routeCost_natDegree_le _ _ B k) hi).trans (by simp [typedSamplerDegree]))
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Cost CL Polynomial
variable {P : Type*} [SizedEncoding P]
theorem typedSampler_haltsWithin (ℓ : ℕ) (S : TypedSampler 3 P) (n B k : ℕ)
    (h : S.TimeBoundAt n B k) (q : Data) :
    HaltsWithin (typedSampler ℓ S).prog (.cons (encode n) q)
      ((typedSamplerCost n B k).eval q.size) := by
  have hr := Prog.routeOneCall_haltsWithin SamplerProgram.route S.closed
    SamplerProgram.post n B k q h (SamplerProgram.route_preserves n q)
  simpa only [typedSampler, SamplerProgram.prog, typedSamplerCost,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Data.size_cons, esize, encode_data, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hr
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Cost CL Polynomial
variable {P : Type*} [SizedEncoding P]
/-- Typed introspection preserves polynomial query time with a common exponent. -/
theorem typedSampler_timeBoundAt (ℓ : ℕ) (S : TypedSampler 3 P) (n B k : ℕ)
    (h : S.TimeBoundAt n B k) :
    (typedSampler ℓ S).TimeBoundAt n (typedSamplerCoefficient n B k) (typedSamplerDegree k) := by
  let Q := typedSamplerCost n B k
  have hQ : (typedSampler ℓ S).TimeBoundAt n (typedSamplerCoefficient n B k) Q.natDegree := by
    intro q
    obtain ⟨r, time, ht, hr⟩ := typedSampler_haltsWithin ℓ S n B k h q
    exact ⟨r, time, ht.trans ((polynomial_eval_mono Q (Nat.le_succ q.size)).trans
      (polynomial_eval_le_sum_coeff_mul_pow Q (by omega))), hr⟩
  exact hQ.mono le_rfl (typedSamplerCost_natDegree_le n B k)
end
end MIPRE.Introspection

namespace MIPRE.Introspection.PauliSampler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL Polynomial
open PauliSamplerParameters
theorem fullSampler_timeBoundAt (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ lam n : ℕ) :
    (fullSampler c hc he ℓ lam).TimeBoundAt n (fullCoefficient c ℓ lam n) (fullDegree ℓ) :=
  CL.Detyping.sampler_timeBoundAt_uniform_degree (graph ℓ)
    (Introspection.typedSampler ℓ (sampler c hc he lam)) (by decide) n
    (Introspection.typedSamplerCoefficient n (coefficient c lam n) degree)
    (Introspection.typedSamplerDegree degree)
    (Introspection.typedSampler_timeBoundAt ℓ (sampler c hc he lam) n
      (coefficient c lam n) degree (sampler_timeBoundAt c hc he lam n))
end
end MIPRE.Introspection.PauliSampler

namespace MIPRE.Introspection.PauliSampler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL Polynomial
open PauliSamplerParameters
theorem fullMajorant_polyBounded (c ℓ : ℕ) : PolyBounded (fullMajorant c ℓ) :=
  routeCost_polyBounded _ _ _
    (routeCost_polyBounded _ _ _ (coefficientMajorant_polyBounded c))
end
end MIPRE.Introspection.PauliSampler

namespace MIPRE.Introspection.PauliSampler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL Polynomial
open PauliSamplerParameters
theorem fullCoefficient_le_majorant {c ℓ lam n v : ℕ} (hc : 1 ≤ c)
    (hl : lam ≤ v) (hn : n ≤ v) (hu : lam * n ≤ v) :
    fullCoefficient c ℓ lam n ≤ fullMajorant c ℓ v := by
  have hnsize : esize n + 2 ≤ 4 * v + 3 := by
    have he := esize_nat_le n
    have hs := (Nat.size_le.mpr Nat.lt_two_pow_self : n.size ≤ n)
    omega
  have hc' := coefficient_le_majorant hc hl hn hu
  have ht : Introspection.typedSamplerCoefficient n (coefficient c lam n) degree ≤
      typedMajorant c v := by
    have he : Introspection.typedSamplerCoefficient n (coefficient c lam n) degree =
        (routeCost Introspection.SamplerProgram.route Introspection.SamplerProgram.post
          (coefficient c lam n) degree).eval (esize n + 2) := by
      simp only [Introspection.typedSamplerCoefficient, Introspection.typedSamplerCost]
      rw [sum_coeff_eq_eval_one]
      simp only [eval_comp, eval_add, eval_X, eval_C]
      congr 1
      omega
    rw [he]
    exact routeCost_eval_mono _ _ _ hc' hnsize
  have he : fullCoefficient c ℓ lam n =
      (routeCost (CL.Detyping.Program.route (graph ℓ))
        (CL.Detyping.Program.post (CL.Detyping.graphDim (QuestionType QLD.Ty ℓ)))
        (Introspection.typedSamplerCoefficient n (coefficient c lam n) degree)
        (Introspection.typedSamplerDegree degree)).eval (esize n + 2) := by
    simp only [fullCoefficient, CL.Detyping.samplerCoefficient, CL.Detyping.samplerCost]
    rw [sum_coeff_eq_eval_one]
    simp only [eval_comp, eval_add, eval_X, eval_C]
    congr 1
    omega
  rw [he]
  exact routeCost_eval_mono _ _ _ ht hnsize
end
end MIPRE.Introspection.PauliSampler

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.PauliSampler
open Cost Cost.Prog Cost.PolyTimeFun CL Polynomial
open PauliSamplerParameters
theorem _root_.solution (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ : ℕ) :
    ∃ C, ∀ lam n, 1 ≤ lam → 1 ≤ n →
      (fullSampler c hc he ℓ lam).TimeBoundAt n ((lam * n + 1) ^ C) C ∧
      (fullSampler c hc he ℓ lam).dim n ≤ (lam * n + 1) ^ C := by
  obtain ⟨D, hD⟩ := ((fullMajorant_polyBounded c ℓ).add
    ((PolyBounded.const (4 * (Fintype.card QLD.Ty + 2 * ℓ + 6))).add
      (dimensionMajorant_polyBounded c))).exists_le_pow
  refine ⟨max D (fullDegree ℓ), fun lam n hl hn => ?_⟩
  have hlv : lam ≤ lam * n + 1 := by nlinarith
  have hnv : n ≤ lam * n + 1 := by nlinarith
  have hv : 2 ≤ lam * n + 1 := by nlinarith
  have hb := hD (lam * n + 1) hv
  have hp : (lam * n + 1) ^ D ≤ (lam * n + 1) ^ max D (fullDegree ℓ) :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hcoef := fullCoefficient_le_majorant (ℓ := ℓ) hc hlv hnv (Nat.le_succ (lam * n))
  have hdim := dimension_le_majorant hc (show lam * n ≤ lam * n + 1 by omega)
  constructor
  · exact (fullSampler_timeBoundAt c hc he ℓ lam n).mono (by omega) (le_max_right _ _)
  · rw [fullSampler_dim]
    omega
end MIPRE.Introspection.PauliSampler

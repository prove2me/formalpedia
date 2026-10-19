-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.exists_intro_bob_iteration
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:51:53.73846+00:00
-- url     : https://prove2.me/submissions/d4b6ee1d-4173-41b7-8a6a-7bcef1a215e0

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveBobIteration.lean (solution of MIPRE.Introspection.TypedEstimates.exists_intro_bob_iteration);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
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
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_StrategyDilation
import Definitions.Def_MIPRE_Foundations_WeylEPR
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
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixFactor
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliRegister
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInitialInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AnswerRefinement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveZFactor
import Definitions.Def_MIPRE_Foundations_Introspection_PauliAuxEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixAdvance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacementRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDilationTransport
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerRefinement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextFactor
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextStrategy
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInduction
import Definitions.Def_MIPRE_Foundations_Introspection_HidingBaseOperators
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageZTests
import Definitions.Def_MIPRE_Foundations_Introspection_IntrospectCanonicalization
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDecodedInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInductionInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_ReadRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDualMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveXSplit
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDualFactor
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageReadTests
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveXTest
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
import Definitions.Def_MIPRE_Foundations_Introspection_RegisteredExtensionErrors
import Definitions.Def_MIPRE_Foundations_Introspection_HidingNormalizerPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidityOrientation
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidityIteration
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidityGame
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInductionStep
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInductionIteration
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePlayerSwap
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveBobIteration
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_exists_intro_iteration
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_parsedGame_value_swap
import Theorems.Thm_MIPRE_swapVec_dotProduct

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
omit [Fintype N] in
theorem evec_sub (v w : N → ℂ) : evec (v - w) = evec v - evec w := rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
theorem xSqNorm_eq_sq (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = xNorm ψ A B ^ 2 := rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
/-- The deviation is the state-norm of the single operator `A ⊗ Id - Id ⊗ B` on the product
space, which is what the operator-norm calculus of `MIPRE/Foundations/OpBound.lean` consumes. -/
theorem xNorm_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xNorm ψ A B = snorm ψ ((aOp A : Matrix (dA × dB) _ ℂ) - bOp B) := by
  rw [xNorm, snorm, Matrix.sub_mulVec, evec_sub]
  rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
/-- The squared cross-party deviation as a `snorm` on the joint space, which is the form the
chains of the appendix are run in. -/
theorem xSqNorm_eq_snorm_sq (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = snorm ψ ((aOp A : Matrix (dA × dB) (dA × dB) ℂ) - bOp B) ^ 2 := by
  rw [xSqNorm_eq_sq, xNorm_eq_snorm]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
omit [DecidableEq dA] in
theorem norm_stateVec_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) :
    ‖stateVec ψ A‖ = snorm ψ (aOp A : Matrix (dA × dB) _ ℂ) := rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
omit [DecidableEq dB] in
theorem norm_stateVecB_eq_snorm (ψ : dA × dB → ℂ) (B : Matrix dB dB ℂ) :
    ‖stateVecB ψ B‖ = snorm ψ (bOp B : Matrix (dA × dB) _ ℂ) := rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
omit [DecidableEq dA] [DecidableEq dB] in
theorem mulVec_kronecker_swapVec (X : Matrix dB dB ℂ) (Y : Matrix dA dA ℂ)
    (ψ : dA × dB → ℂ) :
    (X ⊗ₖ Y) *ᵥ swapVec ψ = swapVec ((Y ⊗ₖ X) *ᵥ ψ) := by
  classical
  funext p
  obtain ⟨j, i⟩ := p
  show ∑ q : dB × dA, (X ⊗ₖ Y) (j, i) q * swapVec ψ q
      = ∑ q : dA × dB, (Y ⊗ₖ X) (i, j) q * ψ q
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
  show X j j' * Y i i' * ψ (i', j') = Y i i' * X j j' * ψ (i', j')
  ring
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
omit [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB] in
theorem swapVec_sub (u v : dA × dB → ℂ) :
    swapVec (u - v) = swapVec u - swapVec v := rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
omit [DecidableEq dA] [DecidableEq dB] in
theorem norm_swapVec (v : dA × dB → ℂ) : ‖evec (swapVec v)‖ = ‖evec v‖ := by
  classical
  rw [evec, evec, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Fintype.sum_equiv (Equiv.prodComm dB dA) _ _ fun _ => rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
/-- **The swap exchanges the two sides of a cross-party deviation.** -/
theorem snorm_swapVec_aOp_sub_bOp (ψ : dA × dB → ℂ) (X : Matrix dB dB ℂ)
    (Y : Matrix dA dA ℂ) :
    snorm (swapVec ψ) ((aOp X : Matrix (dB × dA) (dB × dA) ℂ) - bOp Y) = xNorm ψ Y X := by
  rw [snorm, Matrix.sub_mulVec, aOp, bOp, mulVec_kronecker_swapVec, mulVec_kronecker_swapVec,
    ← swapVec_sub, norm_swapVec, xNorm_eq_snorm, snorm, Matrix.sub_mulVec, aOp, bOp,
    evec_sub, evec_sub, norm_sub_rev]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
omit [DecidableEq dB] in
/-- The same for a single operator on Bob's factor. -/
theorem snorm_swapVec_aOp (ψ : dA × dB → ℂ) (X : Matrix dB dB ℂ) :
    snorm (swapVec ψ) (aOp X : Matrix (dB × dA) (dB × dA) ℂ) = ‖stateVecB ψ X‖ := by
  rw [snorm, aOp, mulVec_kronecker_swapVec, norm_swapVec, norm_stateVecB_eq_snorm, snorm, bOp]
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {I H K : Type*} [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- Swapping the parties swaps only the auxiliary state behind the common
EPR register. -/
theorem swapVec_registerState (ξ : H × K → ℂ) :
    swapVec (registerState I ξ) = registerState I (swapVec ξ) := by
  funext p
  rcases p with ⟨⟨i, k⟩, j, h⟩
  simp [swapVec, registerState, expVec, registerEPR, eq_comm]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {I H K : Type*} [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
theorem xSqNorm_swapVec (ψ : H × K → ℂ)
    (M : Matrix H H ℂ) (N : Matrix K K ℂ) :
    xSqNorm (swapVec ψ) N M = xSqNorm ψ M N := by
  rw [xSqNorm_eq_snorm_sq, snorm_swapVec_aOp_sub_bOp, xSqNorm_eq_sq]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {I H K : Type*} [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
theorem snorm_swapVec_bOp (ψ : H × K → ℂ) (M : Matrix H H ℂ) :
    snorm (swapVec ψ) (bOp M) = snorm ψ (aOp M) := by
  have h := snorm_swapVec_aOp (swapVec ψ) M
  simpa only [swapVec_swapVec, norm_stateVecB_eq_snorm] using h.symm
end
end MIPRE.Introspection

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {I H K : Type*} [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] {ℓ : ℕ}
theorem transposePauliPredicate_transpose
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool) :
    transposePauliPredicate (transposePauliPredicate DP) = DP := rfl
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {I H K : Type*} [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] {ℓ : ℕ}
theorem introBobZError_swap (projectPauli : PauliAnswer → ι → F) (Z : PauliType)
    (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) :
    introBobZError projectPauli Z q (swapVec ξ) MA =
      introAliceZError projectPauli Z q ξ MA := by
  unfold introBobZError introAliceZError
  rw [← swapVec_registerState]
  simp only [snorm_swapVec_bOp, stateSqNorm, stateNorm, norm_stateVec_eq_snorm]
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {I H K : Type*} [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] {ℓ : ℕ}
theorem hidingAliceError_swap (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (j : Fin ℓ) :
    hidingAliceError L w hL (swapVec ξ) MB j = hidingBobError L w hL ξ MB j := by
  unfold hidingAliceError hidingBobError
  rw [← swapVec_registerState]
  simp only [xSqNorm_swapVec]
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {I H K : Type*} [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] {ℓ : ℕ}
theorem hidingBobError_swap (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (j : Fin ℓ) :
    hidingBobError L w hL (swapVec ξ) MA j = hidingAliceError L w hL ξ MA j := by
  have h := hidingAliceError_swap L w hL (swapVec ξ) MA j
  simpa only [swapVec_swapVec] using h.symm
end
end MIPRE.Introspection.TypedEstimates

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {PauliType PauliAnswer κ H : Type*} {F ι A K : Type u}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    (hMA : ∀ q, IsPVM (fun a => ((MA q).mats a).val))
    (hMB : ∀ q, IsPVM (fun a => ((MB q).mats a).val))
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    (w : Bool) (hL : (L w).SupportedOn univ)
    {initial η δ : ℝ} (hi0 : 0 ≤ initial) (hη0 : 0 ≤ η) (hδ0 : 0 ≤ δ)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ initial)
    (hZ : introAliceZError projectPauli Z q ξ MA ≤ η)
    (hhide : ∀ j : Fin ℓ, hidingBobError L w hL ξ MB j ≤ δ)
    (hi : initial ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hη : η ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hδ : δ ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (n : ℕ) (hn : n ≤ ℓ) :
    ∃ (MN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVM (ParsedAnswer (ι → F) A PauliAnswer)
          ((ι → F) × introIterationAux K (Option ((ι → F) × A)) n))
      (_ : IntroPrefixInvariant (L w) n
        ((MN (QuestionType.introspect w, 0)).map introspectPair)),
      (∀ t, IsPVM (fun a => ((MN t).mats a).val)) ∧
      1 - povmValue (parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F)
          (introBobIterationState ξ (none : Option ((ι → F) × A)) n)) MA MN ≤
            adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n ∧
      (∀ t, t ≠ (QuestionType.introspect w, 0) →
        MN t = introIterationExtend (Option ((ι → F) × A)) (MB t) n) ∧
      (∀ j : Fin ℓ, hidingBobError L w hL
        (introBobIterationState ξ (none : Option ((ι → F) × A)) n) MN j =
          hidingBobError L w hL ξ MB j) := by
  have hu : star (swapVec ξ) ⬝ᵥ swapVec ξ = 1 := by rwa [swapVec_dotProduct]
  have hf : 1 - povmValue (parsedGame E X Z P L projectPauli D (transposePauliPredicate DP))
      (registerState (ι → F) (swapVec ξ)) MB MA ≤ initial := by
    rw [parsedGame_value_swap]
    exact hfail
  have hz : introBobZError projectPauli Z q (swapVec ξ) MA ≤ η :=
    (introBobZError_swap projectPauli Z q ξ MA).trans_le hZ
  have hh (j : Fin ℓ) : hidingAliceError L w hL (swapVec ξ) MB j ≤ δ :=
    (hidingAliceError_swap L w hL ξ MB j).trans_le (hhide j)
  obtain ⟨MN, IN, hMN, hfailN, hotherN, hhideN⟩ := exists_intro_iteration
    E X Z P L projectPauli D (transposePauliPredicate DP) (swapVec ξ) hu
    MB MA hMB hMA q hq w hL hi0 hη0 hδ0 hf hz hh hi hη hδ n hn
  refine ⟨MN, IN, hMN, ?_, hotherN, ?_⟩
  · have hv := parsedGame_value_swap E X Z P L projectPauli D (transposePauliPredicate DP)
      (introIterationState (swapVec ξ) (none : Option ((ι → F) × A)) n) MN MA
    simp only [transposePauliPredicate_transpose] at hv
    change 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F)
        (swapVec (introIterationState (swapVec ξ) (none : Option ((ι → F) × A)) n)))
      MA MN ≤ _
    rw [hv]
    exact hfailN
  · intro j
    exact (hidingBobError_swap L w hL
      (introIterationState (swapVec ξ) (none : Option ((ι → F) × A)) n) MN j).trans
      ((hhideN j).trans (hidingAliceError_swap L w hL ξ MB j))
end MIPRE.Introspection.TypedEstimates

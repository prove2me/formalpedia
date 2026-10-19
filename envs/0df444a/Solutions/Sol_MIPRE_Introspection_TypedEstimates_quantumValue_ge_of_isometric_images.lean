-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_isometric_images
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T07:07:27.548233+00:00
-- url     : https://prove2.me/submissions/d075236b-7431-4d0f-b2c4-84b86fb0f011

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/IsometricSoundness.lean (solution of MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_isometric_images);
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
import Definitions.Def_MIPRE_Foundations_Introspection_IsometricStrategy
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
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveTwoSidedIteration
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePowerBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveTerminalInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_TerminalOptionExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_PrimitiveSoundness
import Definitions.Def_MIPRE_Foundations_Introspection_ExtractedStateSoundness
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_quantumValue_ge_of_primitive_pauli
import Theorems.Thm_MIPRE_Introspection_isometricPOVM_map_mats_eq
import Theorems.Thm_MIPRE_Introspection_povmValue_state_stability
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_aOp_zero
import Theorems.Thm_MIPRE_bnd_one_of_conjTranspose_mul_self_le
import Theorems.Thm_MIPRE_norm_evec_expVec

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
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
/-- The sesquilinear form of two matrices applied to the same vector, moved onto one side:
`⟨A v, B v⟩ = ⟨v, A† B v⟩`. -/
theorem star_mulVec_dotProduct {M : Type*} [Fintype M] (A B : Matrix M N ℂ) (v : N → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (B *ᵥ v) = star v ⬝ᵥ ((Aᴴ * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_sq (v : N → ℂ) : ‖evec v‖ ^ 2 = (star v ⬝ᵥ v).re := by
  classical
  rw [evec, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star v i * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [h, Complex.ofReal_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_mulVec_sq {M : Type*} [Fintype M] (A : Matrix M N ℂ) (v : N → ℂ) :
    ‖evec (A *ᵥ v)‖ ^ 2 = (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)).re := by
  rw [norm_evec_sq, star_mulVec_dotProduct]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
/-- **A rectangular isometry preserves the norm.** -/
theorem norm_evec_mulVec_eq {M : Type*} [Fintype M] {A : Matrix M N ℂ} [DecidableEq N]
    (h : Aᴴ * A = 1) (v : N → ℂ) : ‖evec (A *ᵥ v)‖ = ‖evec v‖ := by
  have hsq : ‖evec (A *ᵥ v)‖ ^ 2 = ‖evec v‖ ^ 2 := by
    rw [norm_evec_mulVec_sq, h, Matrix.one_mulVec, norm_evec_sq]
  nlinarith [norm_nonneg (evec (A *ᵥ v)), norm_nonneg (evec v), hsq]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_nonneg (M : Matrix N N ℂ) : 0 ≤ snorm v M := norm_nonneg _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_add_le (M M' : Matrix N N ℂ) : snorm v (M + M') ≤ snorm v M + snorm v M' := by
  rw [snorm, snorm, snorm, Matrix.add_mulVec, evec_add]
  exact norm_add_le _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_mul (X Y : Matrix HB HB ℂ) :
    bOp (X * Y) = (bOp X : Matrix (HA × HB) _ ℂ) * bOp Y := by
  rw [bOp, bOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_add (X Y : Matrix HB HB ℂ) :
    bOp (X + Y) = (bOp X : Matrix (HA × HB) _ ℂ) + bOp Y := Matrix.kronecker_add _ _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_smul (c : ℂ) (X : Matrix HB HB ℂ) :
    bOp (c • X) = c • (bOp X : Matrix (HA × HB) _ ℂ) := Matrix.kronecker_smul _ _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_sub (X Y : Matrix HB HB ℂ) :
    bOp (X - Y) = (bOp X : Matrix (HA × HB) _ ℂ) - bOp Y := by
  have h : X - Y = X + (-1 : ℂ) • Y := by module
  rw [h, bOp_add, bOp_smul]
  module
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_conjTranspose (X : Matrix HB HB ℂ) :
    (bOp X : Matrix (HA × HB) _ ℂ)ᴴ = bOp (Xᴴ) := by
  rw [bOp, bOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
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
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- The triangle inequality for a family of deviations, at the usual cost of a factor two. -/
theorem sum_snorm_sq_triangle' {ι : Type*} [Fintype ι] (v : N → ℂ)
    (P Q R : ι → Matrix N N ℂ) :
    ∑ i, snorm v (P i - R i) ^ 2
      ≤ 2 * ∑ i, snorm v (P i - Q i) ^ 2 + 2 * ∑ i, snorm v (Q i - R i) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsplit : P i - R i = (P i - Q i) + (Q i - R i) := by abel
  have htri : snorm v (P i - R i) ≤ snorm v (P i - Q i) + snorm v (Q i - R i) := by
    rw [hsplit]; exact snorm_add_le v _ _
  nlinarith [snorm_nonneg v (P i - Q i), snorm_nonneg v (Q i - R i),
    snorm_nonneg v (P i - R i), sq_nonneg (snorm v (P i - Q i) - snorm v (Q i - R i))]
end
end MIPRE

namespace MIPRE
section
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder
/-- Pulling a Born-rule expectation back along a linear map `W` conjugates the observable:
`⟨Wv| M |Wv⟩ = ⟨v| Wᴴ M W |v⟩`. With `W` an isometry and `M` a projection this is how a
dilated projective measurement compresses back to the POVM it came from. -/
theorem dotProduct_mulVec_conj {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : Matrix κ ι ℂ) (M : Matrix κ κ ℂ) (v : ι → ℂ) :
    star (W *ᵥ v) ⬝ᵥ (M *ᵥ (W *ᵥ v)) = star v ⬝ᵥ ((Wᴴ * (M * W)) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
/-- **A projection is bounded by the identity.** -/
theorem proj_le_one {P : Matrix N N ℂ} (hsa : Pᴴ = P) (hidem : P * P = P) :
    P ≤ (1 : Matrix N N ℂ) := by
  refine sub_nonneg.mp (Matrix.nonneg_iff_posSemidef.mpr ?_)
  have h : (1 : Matrix N N ℂ) - P = ((1 : Matrix N N ℂ) - P)ᴴ * ((1 : Matrix N N ℂ) - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hsa, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hidem]
    abel
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem norm_evec_eq_one_of_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) : ‖evec ψ‖ = 1 := by
  have h : ‖evec ψ‖ ^ 2 = 1 := by rw [norm_evec_sq, hψ, Complex.one_re]
  nlinarith [norm_nonneg (evec ψ), h]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bOp_zero : (bOp (0 : Matrix dB dB ℂ) : Matrix (dA × dB) (dA × dB) ℂ) = 0 := by
  rw [bOp, Matrix.kronecker_zero]
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
/-- Unit normalization for a nonempty finite EPR basis. -/
theorem registerEPR_norm [Nonempty I] : ‖evec (registerEPR I)‖ = 1 := by
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card I) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  rw [evec, EuclideanSpace.norm_eq]
  simp only [registerEPR, Fintype.sum_prod_type]
  simp only [apply_ite norm, norm_zero, zero_pow (by decide : 2 ≠ 0),
    ite_pow, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hc.le]
  rw [mul_inv_cancel₀ hc.ne', Real.sqrt_one]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
theorem registerState_norm [Nonempty I] (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1) :
    ‖evec (registerState I ξ)‖ = 1 := by
  rw [registerState, norm_evec_expVec, registerEPR_norm, hξ, one_mul]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H R A : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype A]
theorem isometricComplement_mul (V : Matrix R H ℂ) (hV : Vᴴ * V = 1) :
    isometricComplement V * V = 0 := by
  rw [isometricComplement, Matrix.sub_mul, Matrix.one_mul, isometricImage,
    Matrix.mul_one, Matrix.mul_assoc, hV, Matrix.mul_one, sub_self]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H R A : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype A]
/-- The completed measurement intertwines with the original one. -/
theorem isometricEffect_intertwine (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) (M : A → Matrix H H ℂ) (a : A) :
    isometricEffect V a₀ M a * V = V * M a := by
  unfold isometricEffect
  rw [Matrix.add_mul]
  have hi : isometricImage V (M a) * V = V * M a := by
    rw [isometricImage, Matrix.mul_assoc, hV, Matrix.mul_one]
  rw [hi]
  split_ifs <;> simp only [isometricComplement_mul V hV, Matrix.zero_mul, add_zero]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H R A : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype A]
/-- Compression of the completed effect is precisely the source effect. -/
theorem isometricEffect_compress (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) (M : A → Matrix H H ℂ) (a : A) :
    Vᴴ * (isometricEffect V a₀ M a * V) = M a := by
  rw [isometricEffect_intertwine V hV, ← Matrix.mul_assoc, hV, Matrix.one_mul]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H R A : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype A]
theorem isometricPOVM_mats (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) (M : POVM A H) (hM : IsPVM (fun a => (M.mats a).val)) (a : A) :
    ((isometricPOVM V hV a₀ M hM).mats a).val =
      isometricEffect V a₀ (fun a => (M.mats a).val) a := rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H R A : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype A]
theorem isometricPOVM_isPVM (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) (M : POVM A H) (hM : IsPVM (fun a => (M.mats a).val)) :
    IsPVM (fun a => ((isometricPOVM V hV a₀ M hM).mats a).val) :=
  isometricEffect_isPVM V hV a₀ hM
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K R S A B X Y : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
theorem isometricTensor_isometry (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) :
    (V ⊗ₖ W)ᴴ * (V ⊗ₖ W) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    hV, hW, Matrix.one_kronecker_one]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K R S A B X Y : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
theorem isometricState_norm (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) (ψ : H × K → ℂ) :
    ‖evec (isometricState V W ψ)‖ = ‖evec ψ‖ :=
  norm_evec_mulVec_eq (isometricTensor_isometry V W hV hW) ψ
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K R S A B X Y : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
/-- Local completion leaves every individual Born probability unchanged. -/
theorem bornProb_isometricState (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) (ψ : H × K → ℂ)
    (a₀ : A) (b₀ : B) (M : A → Matrix H H ℂ) (N : B → Matrix K K ℂ)
    (a : A) (b : B) :
    bornProb (isometricState V W ψ)
      (isometricEffect V a₀ M a) (isometricEffect W b₀ N b) =
        bornProb ψ (M a) (N b) := by
  rw [bornProb, bornProb, isometricState, dotProduct_mulVec_conj]
  congr 2
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, isometricEffect_compress V hV,
    isometricEffect_compress W hW]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K R S A B X Y : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
/-- Every game value is exactly preserved by the concrete transported PVMs. -/
theorem povmValue_isometricState (G : Game X Y A B)
    (V : Matrix R H ℂ) (W : Matrix S K ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (ψ : H × K → ℂ) (a₀ : A) (b₀ : B)
    (MA : X → POVM A H) (MB : Y → POVM B K)
    (hMA : ∀ x, IsPVM (fun a => ((MA x).mats a).val))
    (hMB : ∀ y, IsPVM (fun b => ((MB y).mats b).val)) :
    povmValue G (isometricState V W ψ)
      (fun x => isometricPOVM V hV a₀ (MA x) (hMA x))
      (fun y => isometricPOVM W hW b₀ (MB y) (hMB y)) = povmValue G ψ MA MB := by
  unfold povmValue condWin
  simp only [isometricPOVM_mats, bornProb_isometricState V W hV hW]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Matrix Finset Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A]
/-- A projection annihilating one vector has at most the squared vector
distance as its mass on another. Normalization is not required. -/
theorem projector_mass_le_state_distance (ψ φ : N → ℂ) (C : Matrix N N ℂ)
    (hC : Cᴴ = C) (hCC : C * C = C) (hz : C *ᵥ ψ = 0) :
    snorm φ C ^ 2 ≤ ‖evec (ψ - φ)‖ ^ 2 := by
  have hb : Bnd C 1 := bnd_one_of_conjTranspose_mul_self_le (by
    rw [hC, hCC]
    exact proj_le_one hC hCC)
  have he : C *ᵥ (φ - ψ) = C *ᵥ φ := by rw [Matrix.mulVec_sub, hz, sub_zero]
  have hn := hb (φ - ψ)
  rw [he, one_mul, evec_sub, norm_sub_rev, ← evec_sub] at hn
  exact sq_le_sq₀ (snorm_nonneg φ C) (norm_nonneg _) |>.mpr hn
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Matrix Finset Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K R S A : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype A]
theorem isometricComplement_alice_mass (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hV : Vᴴ * V = 1) (ψ : H × K → ℂ) (φ : R × S → ℂ) :
    snorm φ (aOp (isometricComplement V)) ^ 2 ≤
      ‖evec (isometricState V W ψ - φ)‖ ^ 2 := by
  apply projector_mass_le_state_distance
  · rw [aOp_conjTranspose, isometricComplement_conjTranspose]
  · rw [← aOp_mul, isometricComplement_idem V hV]
  · rw [isometricState, Matrix.mulVec_mulVec, aOp, ← Matrix.mul_kronecker_mul,
      isometricComplement_mul V hV, Matrix.zero_kronecker, Matrix.zero_mulVec]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Matrix Finset Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K R S A : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype A]
theorem isometricComplement_bob_mass (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hW : Wᴴ * W = 1) (ψ : H × K → ℂ) (φ : R × S → ℂ) :
    snorm φ (bOp (isometricComplement W)) ^ 2 ≤
      ‖evec (isometricState V W ψ - φ)‖ ^ 2 := by
  apply projector_mass_le_state_distance
  · rw [bOp_conjTranspose, isometricComplement_conjTranspose]
  · rw [← bOp_mul, isometricComplement_idem W hW]
  · rw [isometricState, Matrix.mulVec_mulVec, bOp, ← Matrix.mul_kronecker_mul,
      isometricComplement_mul W hW, Matrix.kronecker_zero, Matrix.zero_mulVec]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Matrix Finset Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K R S A : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype A]
/-- Exactly one outcome receives the image complement. -/
theorem isometricEffect_alice_completion_error (V : Matrix R H ℂ) (a₀ : A)
    (M : A → Matrix H H ℂ) (φ : R × S → ℂ) :
    (∑ a, snorm φ (aOp (isometricEffect V a₀ M a - isometricImage V (M a))) ^ 2) =
      snorm φ (aOp (isometricComplement V)) ^ 2 := by
  have he (a : A) : aOp (isometricEffect V a₀ M a - isometricImage V (M a)) =
      if a = a₀ then (aOp (isometricComplement V) : Matrix (R × S) _ ℂ) else 0 := by
    by_cases h : a = a₀ <;> simp [isometricEffect, h, aOp_zero]
  simp_rw [he]
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ h
    simp [h, snorm]
  · simp
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Matrix Finset Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K R S A : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype A]
theorem isometricEffect_bob_completion_error (W : Matrix S K ℂ) (a₀ : A)
    (M : A → Matrix K K ℂ) (φ : R × S → ℂ) :
    (∑ a, snorm φ (bOp (isometricEffect W a₀ M a - isometricImage W (M a))) ^ 2) =
      snorm φ (bOp (isometricComplement W)) ^ 2 := by
  have he (a : A) : bOp (isometricEffect W a₀ M a - isometricImage W (M a)) =
      if a = a₀ then (bOp (isometricComplement W) : Matrix (R × S) _ ℂ) else 0 := by
    by_cases h : a = a₀ <;> simp [isometricEffect, h, bOp_zero]
  simp_rw [he]
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ h
    simp [h, snorm]
  · simp
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Matrix Finset Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K R S A : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype A]
/-- Primitive ideal-state image estimates survive completing the measurement
to a normalized PVM, with no factor for the number of outcomes. -/
theorem isometricEffect_alice_error_le (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hV : Vᴴ * V = 1) (ψ : H × K → ℂ) (φ : R × S → ℂ) (a₀ : A)
    (M : A → Matrix H H ℂ) (Q : A → Matrix R R ℂ) {δ η : ℝ}
    (hδ : ∑ a, snorm φ (aOp (isometricImage V (M a) - Q a)) ^ 2 ≤ δ)
    (hη : ‖evec (isometricState V W ψ - φ)‖ ^ 2 ≤ η) :
    ∑ a, snorm φ (aOp (isometricEffect V a₀ M a - Q a)) ^ 2 ≤ 2 * δ + 2 * η := by
  have h := sum_snorm_sq_triangle' φ (fun a => aOp (isometricEffect V a₀ M a))
    (fun a => aOp (isometricImage V (M a))) (fun a => aOp (Q a))
  simp_rw [← aOp_sub] at h
  rw [isometricEffect_alice_completion_error] at h
  have hc := (isometricComplement_alice_mass V W hV ψ φ).trans hη
  linarith
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Matrix Finset Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K R S A : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype A]
theorem isometricEffect_bob_error_le (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hW : Wᴴ * W = 1) (ψ : H × K → ℂ) (φ : R × S → ℂ) (a₀ : A)
    (M : A → Matrix K K ℂ) (Q : A → Matrix S S ℂ) {δ η : ℝ}
    (hδ : ∑ a, snorm φ (bOp (isometricImage W (M a) - Q a)) ^ 2 ≤ δ)
    (hη : ‖evec (isometricState V W ψ - φ)‖ ^ 2 ≤ η) :
    ∑ a, snorm φ (bOp (isometricEffect W a₀ M a - Q a)) ^ 2 ≤ 2 * δ + 2 * η := by
  have h := sum_snorm_sq_triangle' φ (fun a => bOp (isometricEffect W a₀ M a))
    (fun a => bOp (isometricImage W (M a))) (fun a => bOp (Q a))
  simp_rw [← bOp_sub] at h
  rw [isometricEffect_bob_completion_error] at h
  have hc := (isometricComplement_bob_mass V W hW ψ φ).trans hη
  linarith
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveBudgetCoefficient_pos (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    0 < adaptiveBudgetCoefficient r edges := by
  unfold adaptiveBudgetCoefficient
  positivity
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem iteratedRoot_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ iteratedRoot n t := by
  cases n with
  | zero => exact ht
  | succ n => exact Real.sqrt_nonneg _
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem iteratedRoot_mono (n : ℕ) : Monotone (iteratedRoot n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih => exact fun _ _ h => Real.sqrt_le_sqrt (ih h)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem iteratedRoot_one (n : ℕ) : iteratedRoot n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iteratedRoot, ih, Real.sqrt_one]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem iteratedRoot_le_one (n : ℕ) {t : ℝ} (ht : t ≤ 1) :
    iteratedRoot n t ≤ 1 := by
  simpa only [iteratedRoot_one] using iteratedRoot_mono n ht
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem iteratedRoot_add (m n : ℕ) (t : ℝ) :
    iteratedRoot (m + n) t = iteratedRoot m (iteratedRoot n t) := by
  induction m with
  | zero => simp only [Nat.zero_add, iteratedRoot]
  | succ m ih => simp only [Nat.succ_add, iteratedRoot, ih]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem self_le_iteratedRoot (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ≤ iteratedRoot n t := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact ih.trans (self_le_sqrt_of_unit (iteratedRoot_nonneg n ht0)
      (iteratedRoot_le_one n ht1))
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
/-- A coefficient at least one can be kept unchanged through any fixed
stack of square roots, which is convenient for explicit uniform constants. -/
theorem iteratedRoot_scale_le (n : ℕ) {c t : ℝ} (hc : 1 ≤ c) :
    iteratedRoot n (c * t) ≤ c * iteratedRoot n t := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (Real.sqrt_le_sqrt ih).trans (sqrt_scale_le hc)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptivePowerCoefficient_one_le (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ adaptivePowerCoefficient r edges := by
  unfold adaptivePowerCoefficient
  linarith [adaptiveBudgetCoefficient_pos r hE]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveSoundnessCoefficient_one_le (r n : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ adaptiveSoundnessCoefficient r edges n :=
  (one_le_pow₀ (adaptivePowerCoefficient_one_le r hE)).trans (le_max_left _ _)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]
variable {X Y A B H K : Type*} [Fintype X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- Transfer a game's failure bound to the nearby ideal state. -/
theorem povmValue_failure_transfer (G : Game X Y A B) (ψ φ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (hφ : ‖evec φ‖ = 1)
    (MA : X → POVM A H) (MB : Y → POVM B K)
    (hMA : ∀ x, IsPVM (fun a => ((MA x).mats a).val))
    (hMB : ∀ y, IsPVM (fun b => ((MB y).mats b).val))
    {ε η : ℝ} (hfail : 1 - povmValue G ψ MA MB ≤ ε)
    (hd : ‖evec (ψ - φ)‖ ^ 2 ≤ η) :
    1 - povmValue G φ MA MB ≤ ε + 2 * Real.sqrt η := by
  have h := (abs_le.mp (povmValue_state_stability G ψ φ hψ hφ MA MB hMA hMB hd)).2
  linarith
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
theorem primitiveBudgetCoefficient_bounds (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ primitiveBudgetCoefficient r edges ∧
    4 * edges + 2 ≤ primitiveBudgetCoefficient r edges ∧
    TypedEstimates.hidingPauliBudget r edges 1 1 ≤ primitiveBudgetCoefficient r edges ∧
    4 * edges + 2 * TypedEstimates.hidingPauliBudget r edges 1 1 ≤
      primitiveBudgetCoefficient r edges := by
  have hB : 0 ≤ TypedEstimates.hidingPauliBudget r edges 1 1 := by
    unfold TypedEstimates.hidingPauliBudget
    positivity
  unfold primitiveBudgetCoefficient
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
theorem primitiveSoundnessCoefficient_one_le (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ primitiveSoundnessCoefficient r edges := by
  have hC := adaptiveSoundnessCoefficient_one_le r (2 * r) hE
  have hc := (primitiveBudgetCoefficient_bounds r hE).1
  have hfirst : 1 ≤ (1 + edges) * adaptiveSoundnessCoefficient r edges (2 * r) := by
    nlinarith [mul_nonneg hE (show 0 ≤ adaptiveSoundnessCoefficient r edges (2 * r) by linarith)]
  unfold primitiveSoundnessCoefficient
  nlinarith [mul_nonneg (sub_nonneg.mpr hfirst) (sub_nonneg.mpr hc)]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
theorem extractedSoundnessCoefficient_one_le (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ extractedSoundnessCoefficient r edges := by
  unfold extractedSoundnessCoefficient
  linarith [primitiveSoundnessCoefficient_one_le r hE]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
/-- One additional square root pays for the initial state transfer. -/
theorem extractedSoundness_power_bound (r : ℕ) {edges t : ℝ} (hE : 0 ≤ edges) :
    primitiveSoundnessCoefficient r edges * iteratedRoot (6 * r) (20 * Real.sqrt t) ≤
      extractedSoundnessCoefficient r edges * iteratedRoot (6 * r + 1) t := by
  have h := iteratedRoot_scale_le (6 * r) (t := Real.sqrt t) (by norm_num : (1 : ℝ) ≤ 20)
  have hC := primitiveSoundnessCoefficient_one_le r hE
  have hmul := mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ primitiveSoundnessCoefficient r edges)
  rw [iteratedRoot_add]
  change _ ≤ extractedSoundnessCoefficient r edges * iteratedRoot (6 * r) (Real.sqrt t)
  exact hmul.trans_eq (by unfold extractedSoundnessCoefficient; ring)
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {F ι A H K : Type u} {H₀ K₀ PauliType PauliAnswer κ : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype H₀] [DecidableEq H₀] [Fintype K₀] [DecidableEq K₀]
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (hL : ∀ w, (L w).ExactlyOn univ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (ψ : H₀ × K₀ → ℂ) (hψ : ‖evec ψ‖ = 1)
    (VA : Matrix ((ι → F) × H) H₀ ℂ) (VB : Matrix ((ι → F) × K) K₀ ℂ)
    (hVA : VAᴴ * VA = 1) (hVB : VBᴴ * VB = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H₀)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K₀)
    (hMA : ∀ q, IsPVM (fun a => ((MA q).mats a).val))
    (hMB : ∀ q, IsPVM (fun a => ((MB q).mats a).val))
    (qX qZ : κ → ZMod 2)
    (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
    {t : ℝ} (ht : 0 ≤ t)
    (hstate : ‖evec (isometricState VA VB ψ - registerState (ι → F) ξ)‖ ^ 2 ≤ t)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ t)
    (hX : ∑ x, stateSqNorm (registerState (ι → F) ξ)
      (isometricImage VA
        ((((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val) -
        (aOp (Honest.pauliXReadout x) : Matrix ((ι → F) × H) _ ℂ)) ≤ t)
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      (isometricImage VB
        ((((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).mats z).val) -
        (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ t) :
    1 - extractedSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
      iteratedRoot (6 * ℓ + 1) t ≤ quantumValue G := by
  have hE : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
  have hC := extractedSoundnessCoefficient_one_le ℓ hE
  by_cases ht1 : t ≤ 1
  · let a₀ : ParsedAnswer (ι → F) A PauliAnswer := .pair 0 (Classical.choice inferInstance)
    let NA := fun q => isometricPOVM VA hVA a₀ (MA q) (hMA q)
    let NB := fun q => isometricPOVM VB hVB a₀ (MB q) (hMB q)
    have hNA q : IsPVM (fun a => ((NA q).mats a).val) := isometricPOVM_isPVM _ _ _ _ _
    have hNB q : IsPVM (fun a => ((NB q).mats a).val) := isometricPOVM_isPVM _ _ _ _ _
    have hnψ : ‖evec (isometricState VA VB ψ)‖ = 1 := by
      rw [isometricState_norm VA VB hVA hVB, hψ]
    have hnφ := registerState_norm (I := ι → F) ξ (norm_evec_eq_one_of_unit hξ)
    have hfi : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
        (isometricState VA VB ψ) NA NB ≤ t := by
      rw [show povmValue (parsedGame E X Z P L projectPauli D DP)
        (isometricState VA VB ψ) NA NB =
        povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB from
        povmValue_isometricState _ VA VB hVA hVB ψ a₀ a₀ MA MB hMA hMB]
      exact hfail
    have hf := povmValue_failure_transfer (parsedGame E X Z P L projectPauli D DP)
      (isometricState VA VB ψ) (registerState (ι → F) ξ) hnψ hnφ NA NB hNA hNB hfi hstate
    have hx := isometricEffect_alice_error_le VA VB hVA ψ (registerState (ι → F) ξ)
      (pauliProjection projectPauli a₀)
      (fun x => (((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val)
      (fun x => aOp (Honest.pauliXReadout x))
      (by simpa only [stateSqNorm, stateNorm, norm_stateVec_eq_snorm] using hX) hstate
    have hz := isometricEffect_bob_error_le VA VB hVB ψ (registerState (ι → F) ξ)
      (pauliProjection projectPauli a₀)
      (fun z => (((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).mats z).val)
      (fun z => aOp (readout (some : (ι → F) → Option (ι → F)) z)) hZ hstate
    have hdec : (fun a b : Option (ι → F) => Classical.propDecidable (a = b)) =
        (inferInstance : DecidableEq (Option (ι → F))) := Subsingleton.elim _ _
    have heA (x : Option (ι → F)) :
        (((NA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val =
          isometricEffect VA (pauliProjection projectPauli a₀)
            (fun x => (((MA (QuestionType.pauli X, qX)).map
              (pauliProjection projectPauli)).mats x).val) x := by
      have he := isometricPOVM_map_mats_eq VA hVA a₀ (MA (QuestionType.pauli X, qX))
        (hMA (QuestionType.pauli X, qX)) (pauliProjection projectPauli) x
      rw [hdec] at he
      exact he
    have heB (z : Option (ι → F)) :
        (((NB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).mats z).val =
          isometricEffect VB (pauliProjection projectPauli a₀)
            (fun z => (((MB (QuestionType.pauli Z, qZ)).map
              (pauliProjection projectPauli)).mats z).val) z := by
      have he := isometricPOVM_map_mats_eq VB hVB a₀ (MB (QuestionType.pauli Z, qZ))
        (hMB (QuestionType.pauli Z, qZ)) (pauliProjection projectPauli) z
      rw [hdec] at he
      exact he
    have hx' : ∑ x, stateSqNorm (registerState (ι → F) ξ)
        ((((NA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val -
          (aOp (Honest.pauliXReadout x) : Matrix ((ι → F) × H) _ ℂ)) ≤ 4 * t := by
      simp_rw [heA]
      simpa only [stateSqNorm, stateNorm,
        norm_stateVec_eq_snorm, show 2 * t + 2 * t = 4 * t by ring] using hx
    have hz' : introBobZError projectPauli Z qZ ξ NB ≤ 4 * t := by
      unfold introBobZError
      simp_rw [heB]
      simpa only [show 2 * t + 2 * t = 4 * t by ring] using hz
    have hs := Real.sqrt_nonneg t
    have htr : t ≤ Real.sqrt t := by
      simpa only [iteratedRoot] using self_le_iteratedRoot 1 ht ht1
    have hv := quantumValue_ge_of_primitive_pauli E X Z P L hL projectPauli D DP
      G hμ hD ξ hξ NA NB hNA hNB qX qZ hqX hqZ
      (show 0 ≤ 20 * Real.sqrt t by positivity)
      (hf.trans (by linarith)) (hx'.trans (by linarith)) (hz'.trans (by linarith))
    have hp := extractedSoundness_power_bound ℓ (t := t) hE
    linarith
  · have hroot : 1 ≤ iteratedRoot (6 * ℓ + 1) t := by
      simpa only [iteratedRoot_one] using iteratedRoot_mono (6 * ℓ + 1) (le_of_not_ge ht1)
    have hp : 1 ≤ extractedSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
        iteratedRoot (6 * ℓ + 1) t := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hroot)]
    exact (by linarith : 1 - extractedSoundnessCoefficient ℓ
      (TypeGraph.edges E X Z ℓ).card * iteratedRoot (6 * ℓ + 1) t ≤ 0).trans
      (quantumValue_nonneg G)
end MIPRE.Introspection.TypedEstimates

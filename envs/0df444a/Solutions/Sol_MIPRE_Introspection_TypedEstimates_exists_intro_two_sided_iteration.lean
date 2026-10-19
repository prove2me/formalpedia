-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.exists_intro_two_sided_iteration
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:55:01.158142+00:00
-- url     : https://prove2.me/submissions/60304eab-3967-45db-8b23-d4c21cb32149

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveTwoSidedIteration.lean (solution of MIPRE.Introspection.TypedEstimates.exists_intro_two_sided_iteration);
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
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveTwoSidedIteration
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_exists_intro_bob_iteration
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_exists_intro_iteration
import Theorems.Thm_MIPRE_Introspection_adaptiveFailureBudget_le_threshold
import Theorems.Thm_MIPRE_Introspection_norm_evec_comp_equiv
import Theorems.Thm_MIPRE_Introspection_registerOp_kronecker
import Theorems.Thm_MIPRE_Introspection_registerOp_mulVec
import Theorems.Thm_MIPRE_POVM_map_reindex
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_ancillaEmbed_isometry
import Theorems.Thm_MIPRE_dotProduct_star_self
import Theorems.Thm_MIPRE_kron_one_mul_ancillaEmbed

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open ComplexOrder Matrix
variable {n : Type*} [Fintype n]
variable {X A d : Type*} [Fintype X] [Fintype A] [Fintype d] [DecidableEq d]
/-- **A POVM is determined by its operators.** The remaining fields are propositions. -/
theorem POVM.ext' {M N : POVM A d} (h : ∀ a, (((M.mats a)).val) = (((N.mats a)).val)) : M = N := by
  have hm : M.mats = N.mats := funext fun a => Subtype.ext (h a)
  obtain ⟨mM, hM1, hM2⟩ := M
  obtain ⟨mN, hN1, hN2⟩ := N
  simp only at hm
  subst hm
  rfl
end
end MIPRE

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
/-- **The squared state norm is the quadratic form of `M† M`.** -/
theorem snorm_sq_eq_qform (M : Matrix N N ℂ) : snorm v M ^ 2 = qform v (Mᴴ * M) := by
  rw [snorm, norm_evec_mulVec_sq, qform]
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
open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {A : Type*} [Fintype A] [DecidableEq A]
theorem ancillaEmbed_kron_isometry (a₀ : A) :
    (((ancillaEmbed dA a₀) ⊗ₖ (1 : Matrix dB dB ℂ))ᴴ *
        ((ancillaEmbed dA a₀) ⊗ₖ (1 : Matrix dB dB ℂ)))
      = (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    ancillaEmbed_isometry, Matrix.one_mul, Matrix.one_kronecker_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {A : Type*} [Fintype A] [DecidableEq A]
/-- The extension does not change the norm: the padding is an isometry. -/
theorem norm_evec_extVecA (ψ : dA × dB → ℂ) (a₀ : A) :
    ‖evec (extVecA ψ a₀)‖ = ‖evec ψ‖ :=
  norm_evec_mulVec_eq (ancillaEmbed_kron_isometry a₀) ψ
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {A : Type*} [Fintype A] [DecidableEq A]
/-- The conjugation identity: a quadratic form on the extended state is the quadratic form of the
**compressed** operator on the original one. -/
theorem qform_extVecA (ψ : dA × dB → ℂ) (a₀ : A) (M : Matrix (dA × A) (dA × A) ℂ) :
    qform (extVecA ψ a₀) (aOp M : Matrix ((dA × A) × dB) _ ℂ)
      = qform ψ (aOp ((ancillaEmbed dA a₀)ᴴ * (M * ancillaEmbed dA a₀))) := by
  rw [qform, qform, extVecA, dotProduct_mulVec_conj]
  congr 2
  rw [aOp, aOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem stateSqNorm_eq_qform (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ M = qform ψ ((aOp (Mᴴ * M) : Matrix (dA × dB) _ ℂ)) := by
  rw [stateSqNorm, stateNorm, norm_stateVec_eq_snorm, snorm_sq_eq_qform, aOp_conjTranspose,
    ← aOp_mul]
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
variable {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]
/-- An operator with an inert ancilla compresses to itself. -/
theorem compress_aOp (b₀ : Bnc) (N : Matrix dB dB ℂ) :
    (ancillaEmbed dB b₀)ᴴ * ((aOp N : Matrix (dB × Bnc) _ ℂ) * ancillaEmbed dB b₀) = N := by
  rw [aOp, kron_one_mul_ancillaEmbed,
    ← Matrix.mul_assoc ((ancillaEmbed dB b₀)ᴴ) (ancillaEmbed dB b₀) N, ancillaEmbed_isometry,
    Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] {d E : Type*} [Fintype d] [DecidableEq d] [Fintype E]
  [DecidableEq E]
/-- Extending by the identity commutes with relabelling the outcomes. -/
theorem POVM.map_aOp {B : Type*} [Fintype B] [DecidableEq B] (f : A → B) (M : POVM A d) :
    (M.map f).aOp (E := E) = (M.aOp (E := E)).map f :=
  POVM.ext' fun b => by
    rw [POVM.aOp_mats, POVM.map_mats, POVM.map_mats, aOp_sum]
    rfl
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {I J K L A : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
  [Fintype A] [DecidableEq A]
/-- State distances are unchanged by independent permutations of the two parties. -/
theorem stateSqNorm_registerOp (e : I ≃ J) (f : K ≃ L)
    (ψ : J × L → ℂ) (M : Matrix J J ℂ) :
    stateSqNorm (ψ ∘ e.prodCongr f) (registerOp e M) = stateSqNorm ψ M := by
  unfold stateSqNorm stateNorm stateVec
  change ‖evec _‖ ^ 2 = ‖evec _‖ ^ 2
  rw [← registerOp_one f, ← registerOp_kronecker, registerOp_mulVec, norm_evec_comp_equiv]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K A T : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]
/-- Coordinate formula for adding the same fixed ancilla to every question. -/
theorem extVecA_apply (ψ : H × K → ℂ) (a₀ : T) (h : H) (a : T) (k : K) :
    extVecA ψ a₀ ((h, a), k) = if a = a₀ then ψ (h, k) else 0 := by
  classical
  simp [extVecA, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, ancillaEmbed, Matrix.one_apply, Prod.mk.injEq]
  by_cases ha : a = a₀ <;> simp [ha]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K A T : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]
/-- Extending an old operator by identity preserves its state norm exactly. -/
theorem stateSqNorm_extVecA_aOp (ψ : H × K → ℂ) (a₀ : T) (M : Matrix H H ℂ) :
    stateSqNorm (extVecA ψ a₀) (aOp M) = stateSqNorm ψ M := by
  rw [stateSqNorm_eq_qform, aOp_conjTranspose, ← aOp_mul,
    qform_extVecA, compress_aOp, ← stateSqNorm_eq_qform]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {I H K Y A J : Type*}
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A] [Fintype J]
/-- Dilation changes only the auxiliary state, after the explicit party
reassociation. The original EPR factor is kept exactly. -/
theorem extVecA_registerState (ξ : H × K → ℂ) (a₀ : A) :
    extVecA (registerState I ξ) a₀ =
      registerState I (extVecA ξ a₀) ∘
        (Equiv.prodAssoc I H A).prodCongr (Equiv.refl (I × K)) := by
  funext p
  rcases p with ⟨⟨⟨i, h⟩, a⟩, j, k⟩
  simp only [extVecA_apply, registerState, expVec, Function.comp_apply,
    Equiv.prodCongr_apply, Equiv.prodAssoc_apply, Equiv.refl_apply, Prod.map_fst, Prod.map_snd]
  split_ifs <;> simp
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {X Y A B C H K T : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]
/-- Unit normalization of the actual one-sided ancillary extension. -/
theorem extVecA_unit (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (a₀ : T) :
    star (extVecA ψ a₀) ⬝ᵥ extVecA ψ a₀ = 1 := by
  rw [dotProduct_star_self, norm_evec_extVecA, norm_evec_eq_one_of_unit hψ]
  norm_num
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {X Y A B C I H K T : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
  [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]
/-- Reassociation places the fresh fixed ancilla entirely in the auxiliary
state and leaves the EPR factor literally unchanged. -/
theorem reindex_extVecA_registerState (ξ : H × K → ℂ) (a₀ : T) :
    reindexVec (Equiv.prodAssoc I H T) (Equiv.refl (I × K))
      (extVecA (registerState I ξ) a₀) = registerState I (extVecA ξ a₀) := by
  rw [extVecA_registerState]
  funext p
  simp only [reindexVec, Function.comp_apply, Equiv.apply_symm_apply]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {V I R H K Y A : Type*}
  [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A]
/-- Reassociation transports the squared error exactly to the new register
state, with no state replacement or dimension factor. -/
theorem stateSqNorm_reassociated_extVecA (ξ : H × K → ℂ) (a₀ : A)
    (M : Matrix ((V × H) × A) ((V × H) × A) ℂ) :
    stateSqNorm (registerState V (extVecA ξ a₀))
      (registerOp (Equiv.prodAssoc V H A).symm M) =
      stateSqNorm (extVecA (registerState V ξ) a₀) M := by
  have hs : (extVecA (registerState V ξ) a₀) ∘
      ((Equiv.prodAssoc V H A).symm.prodCongr (Equiv.refl (V × K))) =
        registerState V (extVecA ξ a₀) :=
    reindex_extVecA_registerState ξ a₀
  rw [← hs, stateSqNorm_registerOp]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
section
theorem adaptiveStepLoss_nonneg (δ : ℝ) : 0 ≤ adaptiveStepLoss δ := by
  unfold adaptiveStepLoss
  positivity
end
end MIPRE.Introspection

namespace MIPRE.Introspection
section
theorem adaptiveFailureBudget_step (r n : ℕ) (edges z h initial : ℝ) :
    adaptiveFailureBudget r edges z h initial (n + 1) =
      adaptiveFailureBudget r edges z h initial n +
        adaptiveStepLoss (adaptiveStageBudget r
          (edges * adaptiveFailureBudget r edges z h initial n) z h) := rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
section
theorem adaptiveFailureBudget_mono (r : ℕ) (edges z h initial : ℝ) :
    Monotone (adaptiveFailureBudget r edges z h initial) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [adaptiveFailureBudget_step]
  exact le_add_of_nonneg_right (adaptiveStepLoss_nonneg _)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {H K T H' K' : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]
  [Fintype H'] [DecidableEq H'] [Fintype K'] [DecidableEq K']
theorem xSqNorm_registerOp (e : H' ≃ H) (f : K' ≃ K) (ψ : H × K → ℂ)
    (M : Matrix H H ℂ) (N : Matrix K K ℂ) :
    xSqNorm (ψ ∘ e.prodCongr f) (registerOp e M) (registerOp f N) =
      xSqNorm ψ M N := by
  simp only [xSqNorm_eq_snorm_sq, snorm]
  have h : (aOp (registerOp e M) : Matrix (H' × K') _ ℂ) - bOp (registerOp f N) =
      registerOp (e.prodCongr f) (aOp M - bOp N) := by
    rw [registerOp_sub]
    simp only [aOp, bOp, registerOp_kronecker, registerOp_one]
  rw [h, registerOp_mulVec, norm_evec_comp_equiv]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {H K T H' K' : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]
  [Fintype H'] [DecidableEq H'] [Fintype K'] [DecidableEq K']
/-- The old deviation vector is extended by the same fixed isometry. -/
theorem deviation_extVecA (ψ : H × K → ℂ) (a₀ : T)
    (M : Matrix H H ℂ) (N : Matrix K K ℂ) :
    (aOp (aOp M : Matrix (H × T) _ ℂ) - bOp N) *ᵥ extVecA ψ a₀ =
      extVecA ((aOp M - bOp N) *ᵥ ψ) a₀ := by
  have h : (aOp (aOp M : Matrix (H × T) _ ℂ) - bOp N) *
      (ancillaEmbed H a₀ ⊗ₖ (1 : Matrix K K ℂ)) =
      (ancillaEmbed H a₀ ⊗ₖ (1 : Matrix K K ℂ)) * (aOp M - bOp N) := by
    change ((M ⊗ₖ 1) ⊗ₖ 1 - 1 ⊗ₖ N) * _ = _ * (M ⊗ₖ 1 - 1 ⊗ₖ N)
    rw [Matrix.sub_mul, Matrix.mul_sub]
    simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      kron_one_mul_ancillaEmbed]
  simp only [extVecA, Matrix.mulVec_mulVec, h]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {H K T H' K' : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]
  [Fintype H'] [DecidableEq H'] [Fintype K'] [DecidableEq K']
theorem xSqNorm_extVecA (ψ : H × K → ℂ) (a₀ : T)
    (M : Matrix H H ℂ) (N : Matrix K K ℂ) :
    xSqNorm (extVecA ψ a₀) (aOp M) N = xSqNorm ψ M N := by
  simp only [xSqNorm_eq_snorm_sq, snorm, deviation_extVecA, norm_evec_extVecA]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I H K T A B : Type*}
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T]
  [Fintype A] [Fintype B] [DecidableEq B]
theorem registeredExtendOp_sub (M N : Matrix (I × H) (I × H) ℂ) :
    registeredExtendOp (T := T) (M - N) = registeredExtendOp M - registeredExtendOp N := by
  simp only [registeredExtendOp, aOp_sub, registerOp_sub]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I H K T A B : Type*}
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T]
  [Fintype A] [Fintype B] [DecidableEq B]
/-- Every ideal acting on the original register is literally the same
ideal tensored with the enlarged auxiliary identity. -/
theorem registeredExtendOp_aOp (M : Matrix I I ℂ) :
    registeredExtendOp (H := H) (T := T) (aOp M) = aOp M := by
  ext ⟨i, h, t⟩ ⟨j, h', t'⟩
  by_cases hh : h = h'
  · by_cases ht : t = t' <;>
      simp [registeredExtendOp, aOp, Matrix.kroneckerMap_apply,
        Prod.mk.injEq, hh, ht]
  · simp [registeredExtendOp, aOp, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Prod.mk.injEq, hh]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I H K T A B : Type*}
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T]
  [Fintype A] [Fintype B] [DecidableEq B]
theorem registeredExtendPOVM_map (M : POVM A (I × H)) (f : A → B) :
    registeredExtendPOVM (T := T) (M.map f) = (registeredExtendPOVM M).map f := by
  rw [registeredExtendPOVM, POVM.map_aOp, POVM.map_reindex]
  rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I H K T A B : Type*}
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T]
  [Fintype A] [Fintype B] [DecidableEq B]
theorem stateSqNorm_registeredExtendOp (ξ : H × K → ℂ) (a₀ : T)
    (M : Matrix (I × H) (I × H) ℂ) :
    stateSqNorm (registerState I (extVecA ξ a₀)) (registeredExtendOp M) =
      stateSqNorm (registerState I ξ) M := by
  rw [registeredExtendOp, stateSqNorm_reassociated_extVecA, stateSqNorm_extVecA_aOp]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I H K T A B : Type*}
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T]
  [Fintype A] [Fintype B] [DecidableEq B]
theorem xSqNorm_registeredExtendOp (ξ : H × K → ℂ) (a₀ : T)
    (M : Matrix (I × H) (I × H) ℂ) (N : Matrix (I × K) (I × K) ℂ) :
    xSqNorm (registerState I (extVecA ξ a₀)) (registeredExtendOp M) N =
      xSqNorm (registerState I ξ) M N := by
  have hs := reindex_extVecA_registerState (I := I) ξ a₀
  change (extVecA (registerState I ξ) a₀) ∘
    ((Equiv.prodAssoc I H T).symm.prodCongr (Equiv.refl (I × K))) = _ at hs
  rw [← hs]
  change xSqNorm _ (registerOp (Equiv.prodAssoc I H T).symm (aOp M))
    (registerOp (Equiv.refl (I × K)) N) = _
  rw [xSqNorm_registerOp, xSqNorm_extVecA]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {X I H K T A B : Type*}
  [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T] [Fintype A] [Fintype B] [DecidableEq B]
theorem registeredExtension_bobCrossError
    (ξ : H × K → ℂ) (a₀ : T) (J : B → Matrix I I ℂ)
    (N : B → Matrix (I × K) (I × K) ℂ) :
    (∑ b, xSqNorm (registerState I (extVecA ξ a₀)) (aOp (J b)) (N b)) =
      ∑ b, xSqNorm (registerState I ξ) (aOp (J b)) (N b) := by
  apply Finset.sum_congr rfl
  intro b _
  rw [← registeredExtendOp_aOp, xSqNorm_registeredExtendOp]
end
end MIPRE.Introspection

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K T : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T] {ℓ : ℕ}
theorem hidingBobError_registeredExtension
    (L : Bool → CL.CLFun F ι ℓ) (w : Bool) (hL : (L w).SupportedOn univ)
    (ξ : H × K → ℂ) (a₀ : T)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (j : Fin ℓ) :
    hidingBobError L w hL (extVecA ξ a₀) MB j = hidingBobError L w hL ξ MB j :=
  registeredExtension_bobCrossError ξ a₀ (Honest.hideCoarseOp (L w) j.val hL)
    (fun i => (((MB (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats i).val)
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveFailureBudget_nonneg (r n : ℕ) (edges z h : ℝ)
    {initial : ℝ} (hi : 0 ≤ initial) :
    0 ≤ adaptiveFailureBudget r edges z h initial n := by
  exact hi.trans (adaptiveFailureBudget_mono r edges z h initial (Nat.zero_le n))
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
theorem adaptiveSmallThreshold_pos (r n : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    0 < adaptiveSmallThreshold r edges n := by
  have hC := adaptiveBudgetCoefficient_pos r hE
  induction n with
  | zero => exact div_pos (by norm_num) hC
  | succ n ih =>
    exact lt_min (div_pos ih (by norm_num))
      (div_pos (pow_pos (div_pos ih (by norm_num)) _) hC)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveSmallThreshold_antitone (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    Antitone (adaptiveSmallThreshold r edges) := by
  apply antitone_nat_of_succ_le
  intro n
  calc
    adaptiveSmallThreshold r edges (n + 1) ≤ adaptiveSmallThreshold r edges n / 2 :=
      min_le_left _ _
    _ ≤ adaptiveSmallThreshold r edges n := by
      linarith [adaptiveSmallThreshold_pos r n hE]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {H Ω : Type u} {K : Type*}
  [Fintype H] [DecidableEq H] [Fintype Ω] [DecidableEq Ω]
  [Fintype K] [DecidableEq K]
theorem introIterationState_unit (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (a₀ : Ω) (n : ℕ) :
    star (introIterationState ξ a₀ n) ⬝ᵥ introIterationState ξ a₀ n = 1 := by
  induction n with
  | zero => exact hξ
  | succ n ih => exact extVecA_unit (introIterationState ξ a₀ n) ih a₀
end
end MIPRE.Introspection

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {PauliType PauliAnswer κ K : Type*} {F ι A H : Type u}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem introAliceZError_registeredExtend (projectPauli : PauliAnswer → ι → F)
    (Z : PauliType) (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) :
    introAliceZError projectPauli Z q (extVecA ξ (none : Option ((ι → F) × A)))
      (fun t => registeredExtendPOVM (MA t)) = introAliceZError projectPauli Z q ξ MA := by
  unfold introAliceZError
  apply Finset.sum_congr rfl
  intro z _
  rw [← registeredExtendPOVM_map, registeredExtendPOVM_mats,
    ← registeredExtendOp_aOp, ← registeredExtendOp_sub, stateSqNorm_registeredExtendOp]
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {PauliType PauliAnswer κ K : Type*} {F ι A H : Type u}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
/-- Alice's primitive Z error survives all of Alice's inert Pauli extensions. -/
theorem introAliceZError_introIterationExtend (projectPauli : PauliAnswer → ι → F)
    (Z : PauliType) (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (n : ℕ) :
    introAliceZError projectPauli Z q
      (introIterationState ξ (none : Option ((ι → F) × A)) n)
      (fun t => introIterationExtend (Option ((ι → F) × A)) (MA t) n) =
        introAliceZError projectPauli Z q ξ MA := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (introAliceZError_registeredExtend projectPauli Z q
        (introIterationState ξ (none : Option ((ι → F) × A)) n)
        (fun t => introIterationExtend (Option ((ι → F) × A)) (MA t) n)).trans ih
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {PauliType PauliAnswer κ K : Type*} {F ι A H : Type u}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
/-- The actual Alice-iteration family needs only its exact untouched Pauli
question identity to preserve the primitive input for Bob's block. -/
theorem introAliceZError_of_iteration_other (projectPauli : PauliAnswer → ι → F)
    (Z : PauliType) (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (n : ℕ)
    (MN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer)
        ((ι → F) × introIterationAux H (Option ((ι → F) × A)) n))
    (hother : MN (QuestionType.pauli Z, q) =
      introIterationExtend (Option ((ι → F) × A)) (MA (QuestionType.pauli Z, q)) n) :
    introAliceZError projectPauli Z q
      (introIterationState ξ (none : Option ((ι → F) × A)) n) MN =
        introAliceZError projectPauli Z q ξ MA := by
  have h := introAliceZError_introIterationExtend projectPauli Z q ξ MA n
  simpa only [introAliceZError, hother] using h
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {PauliType PauliAnswer κ K : Type*} {F ι A H : Type u}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
/-- Bob's hiding errors are exactly unchanged during Alice's complete block. -/
theorem hidingBobError_introIterationState (L : Bool → CL.CLFun F ι ℓ)
    (w : Bool) (hL : (L w).SupportedOn univ) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (n : ℕ) (j : Fin ℓ) :
    hidingBobError L w hL (introIterationState ξ (none : Option ((ι → F) × A)) n) MB j =
      hidingBobError L w hL ξ MB j := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (hidingBobError_registeredExtension L w hL
        (introIterationState ξ (none : Option ((ι → F) × A)) n) none MB j).trans ih
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
/-- Restarting the failure recurrence is exactly continuing it. -/
theorem adaptiveFailureBudget_add (r : ℕ) (edges z h initial : ℝ) (m n : ℕ) :
    adaptiveFailureBudget r edges z h initial (m + n) =
      adaptiveFailureBudget r edges z h
        (adaptiveFailureBudget r edges z h initial m) n := by
  induction n with
  | zero => simp only [Nat.add_zero, adaptiveFailureBudget]
  | succ n ih =>
      rw [Nat.add_succ, adaptiveFailureBudget_step, adaptiveFailureBudget_step, ih]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {F ι A H K : Type u}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {PauliType PauliAnswer κ : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
set_option maxHeartbeats 800000 in
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
    (hL : ∀ w, (L w).SupportedOn univ)
    {initial η δ : ℝ} (hi0 : 0 ≤ initial) (hη0 : 0 ≤ η) (hδ0 : 0 ≤ δ)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ initial)
    (hZA : introAliceZError projectPauli Z q ξ MA ≤ η)
    (hZB : introBobZError projectPauli Z q ξ MB ≤ η)
    (hhideA : ∀ j : Fin ℓ, hidingAliceError L false (hL false) ξ MA j ≤ δ)
    (hhideB : ∀ j : Fin ℓ, hidingBobError L true (hL true) ξ MB j ≤ δ)
    (hi : initial ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card (2 * ℓ))
    (hη : η ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card (2 * ℓ))
    (hδ : δ ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card (2 * ℓ)) :
    ∃ (MAN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVM (ParsedAnswer (ι → F) A PauliAnswer)
          ((ι → F) × introIterationAux H (Option ((ι → F) × A)) ℓ))
      (MBN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVM (ParsedAnswer (ι → F) A PauliAnswer)
          ((ι → F) × introIterationAux K (Option ((ι → F) × A)) ℓ))
      (_ : IntroPrefixInvariant (L false) ℓ
        ((MAN (QuestionType.introspect false, 0)).map introspectPair))
      (_ : IntroPrefixInvariant (L true) ℓ
        ((MBN (QuestionType.introspect true, 0)).map introspectPair)),
      (∀ t, IsPVM (fun a => ((MAN t).mats a).val)) ∧
      (∀ t, IsPVM (fun a => ((MBN t).mats a).val)) ∧
      1 - povmValue (parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F) (introTwoSidedState ξ ℓ)) MAN MBN ≤
          adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial (2 * ℓ) := by
  have he : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
  have hlevels : ℓ ≤ 2 * ℓ := by omega
  have ht := adaptiveSmallThreshold_antitone ℓ he hlevels
  obtain ⟨MAN, IA, hMAN, hfA, hoA, _⟩ := exists_intro_iteration
    E X Z P L projectPauli D DP ξ hξ MA MB hMA hMB q hq false (hL false)
    hi0 hη0 hδ0 hfail hZB hhideA (hi.trans ht) (hη.trans ht) (hδ.trans ht) ℓ le_rfl
  have hmid : adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial ℓ ≤
      adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ := by
    simpa only [show 2 * ℓ - ℓ = ℓ by omega] using
      adaptiveFailureBudget_le_threshold ℓ (2 * ℓ) he hi hη hδ ℓ hlevels
  have hzA : introAliceZError projectPauli Z q
      (introIterationState ξ (none : Option ((ι → F) × A)) ℓ) MAN ≤ η := by
    rw [introAliceZError_of_iteration_other projectPauli Z q ξ MA ℓ MAN
      (hoA (QuestionType.pauli Z, q) (by
        intro hh
        have hh' := congrArg Prod.fst hh
        cases hh'))]
    exact hZA
  have hhB (j : Fin ℓ) : hidingBobError L true (hL true)
      (introIterationState ξ (none : Option ((ι → F) × A)) ℓ) MB j ≤ δ := by
    rw [hidingBobError_introIterationState]
    exact hhideB j
  obtain ⟨MBN, IB, hMBN, hfB, _, _⟩ := exists_intro_bob_iteration
    E X Z P L projectPauli D DP
    (introIterationState ξ (none : Option ((ι → F) × A)) ℓ)
    (introIterationState_unit ξ hξ none ℓ) MAN MB hMAN hMB q hq true (hL true)
    (adaptiveFailureBudget_nonneg ℓ ℓ _ η δ hi0) hη0 hδ0 hfA hzA hhB
    hmid (hη.trans ht) (hδ.trans ht) ℓ le_rfl
  refine ⟨MAN, MBN, IA, IB, hMAN, hMBN, ?_⟩
  have hsum := adaptiveFailureBudget_add ℓ (TypeGraph.edges E X Z ℓ).card η δ initial ℓ ℓ
  rw [← two_mul] at hsum
  exact hfB.trans_eq hsum.symm
end MIPRE.Introspection.TypedEstimates

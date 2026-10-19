-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.exists_intro_successor
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:34:31.949184+00:00
-- url     : https://prove2.me/submissions/b03c25d4-ac26-44f4-a749-3079ccc5b5f3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveInductionStep.lean (solution of MIPRE.Introspection.TypedEstimates.exists_intro_successor);
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
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_introspect_refined_stage_bounds
import Theorems.Thm_MIPRE_Introspection_adaptiveRefinedJoint_decode
import Theorems.Thm_MIPRE_Introspection_adaptiveReplacement_distance
import Theorems.Thm_MIPRE_Introspection_advancePrefix_remaining
import Theorems.Thm_MIPRE_Introspection_exists_adaptive_prefix_dilation
import Theorems.Thm_MIPRE_Introspection_norm_evec_comp_equiv
import Theorems.Thm_MIPRE_Introspection_prefixResidual_isPVM
import Theorems.Thm_MIPRE_Introspection_registerOp_isPVM
import Theorems.Thm_MIPRE_Introspection_registerOp_kronecker
import Theorems.Thm_MIPRE_Introspection_registerOp_mulVec
import Theorems.Thm_MIPRE_Introspection_replaceExtended_value
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_POVM_map_map
import Theorems.Thm_MIPRE_POVM_map_reindex
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_ancillaEmbed_isometry
import Theorems.Thm_MIPRE_bornProb_reindex
import Theorems.Thm_MIPRE_kron_one_mul_ancillaEmbed
import Theorems.Thm_MIPRE_norm_evec_expVec
import Theorems.Thm_MIPRE_sum_bornProb_mapA

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
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
/-- **A coarse-graining of a projective POVM is projective**, in the `POVM.map` form the games
use. -/
theorem isPVM_povm_map {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (M : POVM A dA) (h : IsPVM fun a => ((M.mats a).val)) (f : A → B) :
    IsPVM fun b => (((M.map f).mats b).val) := by
  have hval : ∀ b : B, (((M.map f).mats b).val)
      = ∑ a ∈ Finset.univ.filter fun a => f a = b, ((M.mats a).val) := fun b =>
    AddSubmonoidClass.coe_finsetSum _ _
  simpa only [hval] using h.coarse f
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

namespace MIPRE
section
open Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {dA dB dA' dB' : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dA'] [Fintype dB']
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dA'] [DecidableEq dB']
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- **The value of a strategy is invariant under reindexing its registers.** -/
theorem povmValue_reindex (eA : dA ≃ dA') (eB : dB ≃ dB') (G : Game X Y A B)
    (ψ : dA × dB → ℂ) (MA : X → POVM A dA) (MB : Y → POVM B dB) :
    povmValue G (reindexVec eA eB ψ) (fun x => (MA x).reindex eA) (fun y => (MB y).reindex eB)
      = povmValue G ψ MA MB := by
  unfold povmValue condWin
  simp only [POVM.reindex_mats, bornProb_reindex]
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
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {X Y A B C H K : Type*}
  [Fintype X] [Fintype Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- Relabelling a measurement pulls the acceptance predicate back exactly. -/
theorem testAcceptance_map_left (ψ : H × K → ℂ) (D : A → B → Bool)
    (M : POVM C H) (N : POVM B K) (f : C → A) :
    testAcceptance ψ D (fun a => ((M.map f).mats a).val) (fun b => (N.mats b).val) =
      testAcceptance ψ (fun c b => D (f c) b)
        (fun c => (M.mats c).val) (fun b => (N.mats b).val) := by
  unfold testAcceptance
  rw [Finset.sum_comm]
  simp_rw [sum_bornProb_mapA M f]
  exact Finset.sum_comm
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
theorem replaceExtended_other (MA : X → POVM A H) (q x : X) (R : POVM A (H × T))
    (hx : x ≠ q) : replaceExtended MA q R x = (MA x).aOp := by
  simp [replaceExtended, hx]
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
theorem replaceExtended_isPVM (MA : X → POVM A H) (q : X) (R : POVM A (H × T))
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hR : IsPVM fun a => (R.mats a).val) (x : X) :
    IsPVM (fun a => ((replaceExtended MA q R x).mats a).val) := by
  by_cases hx : x = q
  · simpa only [hx, replaceExtended_at] using hR
  · simpa only [replaceExtended_other MA q x R hx, POVM.aOp_mats] using (hMA x).aOp
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
theorem povm_reindex_refl (M : POVM A H) : M.reindex (Equiv.refl H) = M :=
  POVM.ext' fun _ => rfl
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
variable {X Y A B C I H K T : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
  [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]
theorem registeredReplacement_other (MA : X → POVM A (I × H)) (q x : X)
    (R : POVM A ((I × H) × T)) (hx : x ≠ q) :
    registeredReplacement MA q R x = ((MA x).aOp).reindex (Equiv.prodAssoc I H T) := by
  simp only [registeredReplacement, replaceExtended_other MA q x R hx]
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
theorem registeredReplacement_isPVM (MA : X → POVM A (I × H)) (q : X)
    (R : POVM A ((I × H) × T))
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hR : IsPVM fun a => (R.mats a).val) (x : X) :
    IsPVM (fun a => ((registeredReplacement MA q R x).mats a).val) :=
  registerOp_isPVM (Equiv.prodAssoc I H T).symm (replaceExtended_isPVM MA q R hMA hR x)
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
/-- The registered replacement and its unreassociated version have exactly
the same value, for every game. -/
theorem registeredReplacement_value_eq (G : Game X Y A B) (ξ : H × K → ℂ) (a₀ : T)
    (MA : X → POVM A (I × H)) (MB : Y → POVM B (I × K)) (q : X)
    (R : POVM A ((I × H) × T)) :
    povmValue G (registerState I (extVecA ξ a₀)) (registeredReplacement MA q R) MB =
      povmValue G (extVecA (registerState I ξ) a₀) (replaceExtended MA q R) MB := by
  have h := povmValue_reindex (Equiv.prodAssoc I H T) (Equiv.refl (I × K)) G
    (extVecA (registerState I ξ) a₀) (replaceExtended MA q R) MB
  change povmValue G (registerState I (extVecA ξ a₀))
    (fun x => (replaceExtended MA q R x).reindex (Equiv.prodAssoc I H T)) MB = _
  simpa only [reindex_extVecA_registerState, povm_reindex_refl] using h
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem adaptiveOldJointPOVM_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val)) :
    IsPVM (fun p => ((adaptiveOldJointPOVM P hP k M hM).mats p).val) :=
  prefixResidual_isPVM P hP k (fun y p => ((M y).mats p).val) hM
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem adaptiveReplacementPOVM_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z)) :
    IsPVM (fun p => ((adaptiveReplacementPOVM P hP k D hD).mats p).val) :=
  registerOp_isPVM (Equiv.prodAssoc (ι → F) H A)
    (adaptiveReplacementJointOp_isPVM P hP k D hD)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
/-- Once the next prefix is named, the update depends only on that prefix
and its remaining answer tail. -/
theorem stageAnswerDecode_next {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (a : Option ((ι → F) × A)) :
    stageAnswerDecode P k y z a = a.map (fun p =>
      (advancePrefix P k y z +
        CL.proj (stageRemaining P (k + 1) (advancePrefix P k y z)) p.1, p.2)) := by
  cases a <;> simp [stageAnswerDecode, advancePrefix_remaining hP]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {V A PauliAnswer : Type*}
variable {F ι PauliType : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem check_canonicalIntroAnswer_left
    (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (w : Bool) (t : QuestionType PauliType ℓ)
    (a b : ParsedAnswer (ι → F) A PauliAnswer) :
    TypedPredicate.check L X Z projectPauli D DP (QuestionType.introspect w) t
      (canonicalIntroAnswer a) b =
      TypedPredicate.check L X Z projectPauli D DP (QuestionType.introspect w) t a b := by
  cases a
  case pair => rfl
  all_goals simp [canonicalIntroAnswer, restoreIntroAnswer, TypedEstimates.introspectPair,
    TypedPredicate.check, TypedPredicate.fits]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {V A PauliAnswer : Type*}
variable {F ι PauliType κ H : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype PauliType] [DecidableEq PauliType]
  [Fintype κ] [DecidableEq κ] [Fintype H] [DecidableEq H]
  [Fintype A] [Fintype PauliAnswer] {ℓ : ℕ}
theorem canonicalizeIntro_at
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H) (w : Bool) :
    canonicalizeIntro MA w (QuestionType.introspect w, 0) =
      (MA (QuestionType.introspect w, 0)).map canonicalIntroAnswer := by
  simp [canonicalizeIntro]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {V A PauliAnswer : Type*}
variable {F ι PauliType κ H : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype PauliType] [DecidableEq PauliType]
  [Fintype κ] [DecidableEq κ] [Fintype H] [DecidableEq H]
  [Fintype A] [Fintype PauliAnswer] {ℓ : ℕ}
theorem canonicalizeIntro_other
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H) (w : Bool)
    (q : CL.Detyping.Question (QuestionType PauliType ℓ) κ)
    (hq : q ≠ (QuestionType.introspect w, 0)) : canonicalizeIntro MA w q = MA q := by
  simp only [canonicalizeIntro, if_neg hq]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {V A PauliAnswer : Type*}
variable {F ι PauliType κ H : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype PauliType] [DecidableEq PauliType]
  [Fintype κ] [DecidableEq κ] [Fintype H] [DecidableEq H]
  [Fintype A] [Fintype PauliAnswer] {ℓ : ℕ}
theorem canonicalizeIntro_factor
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H) (w : Bool) :
    canonicalizeIntro MA w (QuestionType.introspect w, 0) =
      ((MA (QuestionType.introspect w, 0)).map TypedEstimates.introspectPair).map
        restoreIntroAnswer := by
  rw [canonicalizeIntro_at, POVM.map_map]
  rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {V A PauliAnswer : Type*}
variable {F ι PauliType PauliAnswer κ A H K : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer] [Fintype A]
  [Fintype κ] [DecidableEq κ] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem canonicalizeIntro_condWin
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ψ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K)
    (w : Bool) (q r : CL.Detyping.Question (QuestionType PauliType ℓ) κ) :
    condWin (parsedGame E X Z P L projectPauli D DP) ψ (canonicalizeIntro MA w) MB q r =
      condWin (parsedGame E X Z P L projectPauli D DP) ψ MA MB q r := by
  by_cases hq : q = (QuestionType.introspect w, 0)
  · subst q
    change testAcceptance ψ (questionCheck L X Z projectPauli D DP (QuestionType.introspect w, 0) r)
      (fun a => ((canonicalizeIntro MA w (QuestionType.introspect w, 0)).mats a).val)
      (fun b => ((MB r).mats b).val) = _
    rw [canonicalizeIntro_at, testAcceptance_map_left]
    have hd : (fun a b => questionCheck L X Z projectPauli D DP
        (QuestionType.introspect w, 0) r (canonicalIntroAnswer a) b) =
        questionCheck L X Z projectPauli D DP (QuestionType.introspect w, 0) r := by
      funext a b
      exact check_canonicalIntroAnswer_left L X Z projectPauli D _ w r.1 a b
    rw [hd]
    rfl
  · simp only [condWin, canonicalizeIntro_other MA w q hq]
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {V A PauliAnswer : Type*}
variable {F ι PauliType PauliAnswer κ A H K : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer] [Fintype A]
  [Fintype κ] [DecidableEq κ] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] {ℓ : ℕ}
/-- Format normalization has exactly the original parsed-game value,
including the entire malformed-answer mass. -/
theorem canonicalizeIntro_value
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ψ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K) (w : Bool) :
    povmValue (parsedGame E X Z P L projectPauli D DP) ψ (canonicalizeIntro MA w) MB =
      povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB := by
  simp only [povmValue, canonicalizeIntro_condWin]
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem stageAnswerDecode_nextOptionDecoder {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F)
    (a : Option ((ι → F) × A)) :
    stageAnswerDecode P k y z a = nextOptionDecoder P k (advancePrefix P k y z, a) :=
  stageAnswerDecode_next hP k y z a
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem nextOptionDecoder_advanceStageAnswer {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ)
    (p : AdaptiveStageAnswer P k (Option ((ι → F) × A))) :
    nextOptionDecoder P k (advanceStageAnswer P k p) =
      stageAnswerDecode P k p.1 p.2.1 p.2.2 :=
  (stageAnswerDecode_nextOptionDecoder hP k p.1 p.2.1 p.2.2).symm
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {F ι H A B C : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype H] [DecidableEq H]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C] {ℓ : ℕ}
/-- The same exact recovery uses only the advanced prefix and the retained
answer, which is the decoder interface of the next-strategy theorem. -/
theorem adaptiveRefinedJoint_next_decode (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → POVM (Option ((ι → F) × A))
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun a => ((M y).mats a).val))
    (N : POVM (Option ((ι → F) × A)) ((ι → F) × H))
    (hform : ∀ a, (N.mats a).val = ∑ y, prefixResidualOp P k y ((M y).mats a).val)
    (hsupport : ∀ y x a, P.outputPrefix k x ≠ y → ((M y).mats (some (x, a))).val = 0) :
    (adaptiveOldJointPOVM P hP k
      (fun y => stageAnswerRefinementPOVM P k y (M y))
      (fun y => stageAnswerRefinementPOVM_isPVM P k y (M y) (hM y))).map
        (fun p => nextOptionDecoder P k (advanceStageAnswer P k p)) = N := by
  simp only [nextOptionDecoder_advanceStageAnswer hP]
  exact adaptiveRefinedJoint_decode P hP k M hM N hform hsupport
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {F ι H A B C : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype H] [DecidableEq H]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C] {ℓ : ℕ}
variable {PauliType PauliAnswer κ T : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] [Fintype T] [DecidableEq T]
/-- The raw normalized Introspect POVM is exactly the refined old joint
PVM followed by the actual updating decoder and raw-answer restoration. -/
theorem canonicalizeIntro_adaptive_selected (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (w : Bool)
    (M : (y : ι → F) → POVM (Option ((ι → F) × A))
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun a => ((M y).mats a).val))
    (hform : ∀ a, (((MA (QuestionType.introspect w, 0)).map
      TypedEstimates.introspectPair).mats a).val =
        ∑ y, prefixResidualOp P k y ((M y).mats a).val)
    (hsupport : ∀ y x a, P.outputPrefix k x ≠ y → ((M y).mats (some (x, a))).val = 0) :
    canonicalizeIntro MA w (QuestionType.introspect w, 0) =
      (adaptiveOldJointPOVM P hP k
        (fun y => stageAnswerRefinementPOVM P k y (M y))
        (fun y => stageAnswerRefinementPOVM_isPVM P k y (M y) (hM y))).map
          (fun p => restoreIntroAnswer (nextOptionDecoder P k (advanceStageAnswer P k p))) := by
  rw [canonicalizeIntro_factor]
  have hd := adaptiveRefinedJoint_next_decode P hP k M hM
    ((MA (QuestionType.introspect w, 0)).map TypedEstimates.introspectPair) hform hsupport
  rw [← hd, POVM.map_map]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {F ι H A B C : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype H] [DecidableEq H]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C] {ℓ : ℕ}
variable {PauliType PauliAnswer κ T : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] [Fintype T] [DecidableEq T]
/-- Canonicalization at the selected question is overwritten by the actual
replacement. All other old questions are retained identically. -/
theorem registeredReplacement_canonicalizeIntro
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (w : Bool)
    (R : POVM (ParsedAnswer (ι → F) A PauliAnswer) (((ι → F) × H) × T)) :
    registeredReplacement (canonicalizeIntro MA w) (QuestionType.introspect w, 0) R =
      registeredReplacement MA (QuestionType.introspect w, 0) R := by
  funext q
  by_cases hq : q = (QuestionType.introspect w, 0)
  · subst q
    simp only [registeredReplacement_at]
  · rw [registeredReplacement_other (canonicalizeIntro MA w) _ q R hq,
      registeredReplacement_other MA _ q R hq, canonicalizeIntro_other MA w q hq]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
section
theorem adaptiveStageBudget_nonneg (r : ℕ) {e z h : ℝ}
    (he : 0 ≤ e) (hz : 0 ≤ z) (hh : 0 ≤ h) :
    0 ≤ adaptiveStageBudget r e z h := by
  unfold adaptiveStageBudget
  positivity
end
end MIPRE.Introspection

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
variable
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
  {ε η δ : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
  (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
    (registerState (ι → F) ξ) MA MB ≤ ε)
  (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
  (w : Bool) (hL : (L w).SupportedOn univ) (j : Fin ℓ)
  (hSA : IsPVM (fun a => ((MA (QuestionType.sample w, 0)).mats a).val))
  (hSB : IsPVM (fun a => ((MB (QuestionType.sample w, 0)).mats a).val))
  (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
    ((((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val -
      (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
        Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ η)
  (hHide : IsPVM (fun a => ((MA (QuestionType.hide w j, 0)).mats a).val))
  (hRead : IsPVM (fun a => ((MB (QuestionType.read w, 0)).mats a).val))
  (hfine : ∑ i, xSqNorm (registerState (ι → F) ξ)
    ((((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats i).val)
    (aOp (Honest.hideCoarseOp (L w) j.val hL i) : Matrix ((ι → F) × K) _ ℂ) ≤ δ)
  (M : (y : ι → F) → POVM (Option ((ι → F) × A))
    ((stageRemaining (L w) j.val y → F) × H))
  (hform : ∀ a, (((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val =
    ∑ y, prefixResidualOp (L w) j.val y ((M y).mats a).val)
  (hsupport : ∀ y x a, (L w).outputPrefix j.val x ≠ y →
    ((M y).mats (some (x, a))).val = 0)
include hξ hε hη hδ hfail hq hSA hSB hZ hHide hRead hfine hform hsupport
set_option backward.isDefEq.respectTransparency false in
/-- Actual game tests construct the common-ancilla adaptive projectors.
Only the current prefix product form and its answer support are structural
inputs; none of the three analytic mixing estimates is assumed. -/
theorem exists_game_adaptive_prefix_dilation
    (hM : ∀ y, IsPVM (fun a => ((M y).mats a).val))
    (hsmall : adaptiveStageBudget (ℓ - j.val)
      ((TypeGraph.edges E X Z ℓ).card * ε) η δ ≤ 1) :
    ∃ (R : AdaptiveDilationFamily (L w) j.val H (Option ((ι → F) × A)))
      (hR : ∀ y z, IsPVM (R y z)),
      (∑ p, stateSqNorm (extVecA (registerState (ι → F) ξ) (none : Option ((ι → F) × A)))
        (aOp ((adaptiveOldJointPOVM (L w) hL j.val
          (fun y => stageAnswerRefinementPOVM (L w) j.val y (M y))
          (fun y => stageAnswerRefinementPOVM_isPVM (L w) j.val y (M y) (hM y))).mats p).val -
            ((adaptiveReplacementPOVM (L w) hL j.val R hR).mats p).val)) ≤
        2 * Real.sqrt (56 * Real.sqrt (adaptiveStageBudget (ℓ - j.val)
          ((TypeGraph.edges E X Z ℓ).card * ε) η δ)) := by
  have hb := introspect_refined_stage_bounds E X Z P L projectPauli D DP ξ hξ MA MB
    hε hη hδ hfail q hq w hL j hSA hSB hZ hHide hRead hfine M hform hsupport
  have hb0 := adaptiveStageBudget_nonneg (ℓ - j.val)
    (mul_nonneg (Nat.cast_nonneg (TypeGraph.edges E X Z ℓ).card) hε) hη hδ
  obtain ⟨R, hR, hd⟩ := exists_adaptive_prefix_dilation (L w) hL j.val ξ
    (norm_evec_eq_one_of_unit hξ) (none : Option ((ι → F) × A))
    (fun y => stageAnswerRefinementPOVM (L w) j.val y (M y))
    (fun y => stageAnswerRefinementPOVM_isPVM (L w) j.val y (M y) (hM y))
    hb0 hsmall hb.1 hb.2.1 hb.2.2
  exact ⟨R, hR, adaptiveReplacement_distance (L w) hL j.val ξ none _ _ R hR hd⟩
end
end MIPRE.Introspection.TypedEstimates

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
theorem registeredReplacement_other_eq (MA : X → POVM A (I × H)) (q x : X)
    (R : POVM A ((I × H) × T)) (hx : x ≠ q) :
    registeredReplacement MA q R x = registeredExtendPOVM (MA x) :=
  registeredReplacement_other MA q x R hx
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
/-- Outcome maps, including their malformed outcome, are transported exactly. -/
theorem registeredReplacement_other_map (MA : X → POVM A (I × H)) (q x : X)
    (R : POVM A ((I × H) × T)) (hx : x ≠ q) (f : A → B) :
    (registeredReplacement MA q R x).map f = registeredExtendPOVM ((MA x).map f) := by
  rw [registeredReplacement_other_eq MA q x R hx, registeredExtendPOVM_map]
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
theorem registeredReplacement_crossError_other
    (ξ : H × K → ℂ) (a₀ : T) (MA : X → POVM A (I × H)) (q x : X)
    (R : POVM A ((I × H) × T)) (hx : x ≠ q) (f : A → B)
    (N : B → Matrix (I × K) (I × K) ℂ) :
    (∑ b, xSqNorm (registerState I (extVecA ξ a₀))
      ((((registeredReplacement MA q R x).map f).mats b).val) (N b)) =
      ∑ b, xSqNorm (registerState I ξ) ((((MA x).map f).mats b).val) (N b) := by
  rw [registeredReplacement_other_map MA q x R hx f]
  simp only [registeredExtendPOVM_mats, xSqNorm_registeredExtendOp]
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
theorem hidingAliceError_registeredReplacement
    (L : Bool → CL.CLFun F ι ℓ) (w v : Bool) (hL : (L w).SupportedOn univ)
    (ξ : H × K → ℂ) (a₀ : T)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (R : POVM (ParsedAnswer (ι → F) A PauliAnswer) (((ι → F) × H) × T)) (j : Fin ℓ) :
    hidingAliceError L w hL (extVecA ξ a₀)
      (registeredReplacement MA (QuestionType.introspect v, 0) R) j =
      hidingAliceError L w hL ξ MA j := by
  exact registeredReplacement_crossError_other ξ a₀ MA _ _ R (by simp)
    (hidingCoarse (L w) j.val) (fun i => aOp (Honest.hideCoarseOp (L w) j.val hL i))
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem introSuccessorFamily_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (w : Bool)
    (R : AdaptiveDilationFamily P k H (Option ((ι → F) × A)))
    (hR : ∀ y z, IsPVM (R y z))
    (hMA : ∀ q, IsPVM (fun a => ((MA q).mats a).val))
    (q : CL.Detyping.Question (QuestionType PauliType ℓ) κ) :
    IsPVM (fun a => ((introSuccessorFamily P hP k MA w R hR q).mats a).val) := by
  apply registeredReplacement_isPVM _ _ _ hMA
  exact isPVM_povm_map _ (adaptiveReplacementPOVM_isPVM P hP k R hR) _
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] {ℓ : ℕ}
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
    (w : Bool) (hL : (L w).SupportedOn univ) (j : Fin ℓ)
    (I : IntroPrefixInvariant (L w) j.val
      ((MA (QuestionType.introspect w, 0)).map introspectPair))
    {ε η δ : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (hZ : introBobZError projectPauli Z q ξ MB ≤ η)
    (hhide : hidingAliceError L w hL ξ MA j ≤ δ)
    (hsmall : adaptiveStageBudget (ℓ - j.val)
      ((TypeGraph.edges E X Z ℓ).card * ε) η δ ≤ 1) :
    ∃ (MA' : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVM (ParsedAnswer (ι → F) A PauliAnswer)
          ((ι → F) × (H × Option ((ι → F) × A))))
      (_ : IntroPrefixInvariant (L w) (j.val + 1)
        ((MA' (QuestionType.introspect w, 0)).map introspectPair)),
      (∀ t, IsPVM (fun a => ((MA' t).mats a).val)) ∧
      1 - povmValue (parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F) (extVecA ξ (none : Option ((ι → F) × A)))) MA' MB ≤
          ε + adaptiveStepLoss (adaptiveStageBudget (ℓ - j.val)
            ((TypeGraph.edges E X Z ℓ).card * ε) η δ) ∧
      (∀ t, t ≠ (QuestionType.introspect w, 0) → MA' t = registeredExtendPOVM (MA t)) ∧
      (∀ i : Fin ℓ, hidingAliceError L w hL
        (extVecA ξ (none : Option ((ι → F) × A))) MA' i = hidingAliceError L w hL ξ MA i) := by
  obtain ⟨R, hR, hd⟩ := exists_game_adaptive_prefix_dilation E X Z P L projectPauli D DP
    ξ hξ MA MB hε hη hδ hfail q hq w hL j
    (hMA _) (hMB _) hZ (hMA _) (hMB _) hhide
    I.residual I.form I.support I.projective hsmall
  let J := adaptiveOldJointPOVM (L w) hL j.val
    (fun y => stageAnswerRefinementPOVM (L w) j.val y (I.residual y))
    (fun y => stageAnswerRefinementPOVM_isPVM (L w) j.val y (I.residual y) (I.projective y))
  let N := adaptiveReplacementPOVM (L w) hL j.val R hR
  let f := fun p : AdaptiveStageAnswer (L w) j.val (Option ((ι → F) × A)) =>
    restoreIntroAnswer (PauliAnswer := PauliAnswer)
      (nextOptionDecoder (L w) j.val (advanceStageAnswer (L w) j.val p))
  have hselected : canonicalizeIntro MA w (QuestionType.introspect w, 0) = J.map f :=
    canonicalizeIntro_adaptive_selected (L w) hL j.val MA w
      I.residual I.projective I.form I.support
  have hv := replaceExtended_value (parsedGame E X Z P L projectPauli D DP)
    (registerState (ι → F) ξ) (registerState_norm ξ (norm_evec_eq_one_of_unit hξ))
    (none : Option ((ι → F) × A)) (canonicalizeIntro MA w) MB
    (QuestionType.introspect w, 0) J N f hselected
    (adaptiveOldJointPOVM_isPVM (L w) hL j.val _ _) (adaptiveReplacementPOVM_isPVM _ _ _ R hR)
    hMB hd
  rw [← registeredReplacement_value_eq (parsedGame E X Z P L projectPauli D DP)
      ξ none (canonicalizeIntro MA w) MB (QuestionType.introspect w, 0) (N.map f),
    canonicalizeIntro_value, registeredReplacement_canonicalizeIntro] at hv
  refine ⟨introSuccessorFamily (L w) hL j.val MA w R hR,
    introSuccessorInvariant (L w) hL j.val MA w R hR,
    introSuccessorFamily_isPVM (L w) hL j.val MA w R hR hMA, ?_, ?_, ?_⟩
  · have hloss := (abs_sub_le_iff.mp hv).1
    change 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) (extVecA ξ (none : Option ((ι → F) × A))))
      (registeredReplacement MA (QuestionType.introspect w, 0) (N.map f)) MB ≤ _
    unfold adaptiveStepLoss
    linarith
  · intro t ht
    exact registeredReplacement_other_eq MA (QuestionType.introspect w, 0) t (N.map f) ht
  · intro i
    exact hidingAliceError_registeredReplacement L w w hL ξ none MA (N.map f) i
end MIPRE.Introspection.TypedEstimates

-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.exists_intro_iteration
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:40:47.649432+00:00
-- url     : https://prove2.me/submissions/d16c3edb-8448-441e-89ff-7f349d6f895d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveInductionIteration.lean (solution of MIPRE.Introspection.TypedEstimates.exists_intro_iteration);
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
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_exists_intro_successor
import Theorems.Thm_MIPRE_Introspection_adaptiveFailureBudget_le_threshold
import Theorems.Thm_MIPRE_Introspection_norm_evec_comp_equiv
import Theorems.Thm_MIPRE_Introspection_registerOp_kronecker
import Theorems.Thm_MIPRE_Introspection_registerOp_mulVec
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_aOp_zero
import Theorems.Thm_MIPRE_ancillaEmbed_isometry
import Theorems.Thm_MIPRE_dotProduct_star_self
import Theorems.Thm_MIPRE_kron_one_mul_ancillaEmbed

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
theorem snorm_sub_comm (M M' : Matrix N N ℂ) : snorm v (M - M') = snorm v (M' - M) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, evec_sub, evec_sub, norm_sub_rev]
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
section
theorem adaptiveStepLoss_nonneg (δ : ℝ) : 0 ≤ adaptiveStepLoss δ := by
  unfold adaptiveStepLoss
  positivity
end
end MIPRE.Introspection

namespace MIPRE.Introspection
section
theorem adaptiveStepLoss_mono {δ η : ℝ} (h : δ ≤ η) :
    adaptiveStepLoss δ ≤ adaptiveStepLoss η := by
  unfold adaptiveStepLoss
  gcongr
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
variable {I H K T A B : Type*}
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T]
  [Fintype A] [Fintype B] [DecidableEq B]
/-- Bob's same-party error is unaffected by adding an auxiliary register
on Alice's side, including the exact registered state reassociation. -/
theorem snorm_bOp_registered_extVecA (ξ : H × K → ℂ) (a₀ : T)
    (N : Matrix (I × K) (I × K) ℂ) :
    snorm (registerState I (extVecA ξ a₀)) (bOp N) ^ 2 =
      snorm (registerState I ξ) (bOp N) ^ 2 := by
  have h := xSqNorm_registeredExtendOp ξ a₀ (0 : Matrix (I × H) _ ℂ) N
  rw [registeredExtendOp_zero, xSqNorm_eq_snorm_sq, aOp_zero,
    snorm_sub_comm, sub_zero, xSqNorm_eq_snorm_sq, aOp_zero,
    snorm_sub_comm, sub_zero] at h
  exact h
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
theorem registeredExtension_bobSamePartyError
    (ξ : H × K → ℂ) (a₀ : T) (N : B → Matrix (I × K) (I × K) ℂ) :
    (∑ b, snorm (registerState I (extVecA ξ a₀)) (bOp (N b)) ^ 2) =
      ∑ b, snorm (registerState I ξ) (bOp (N b)) ^ 2 := by
  simp only [snorm_bOp_registered_extVecA]
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
/-- The primitive Bob Pauli estimate is unchanged on the newly extended
state; Bob's actual family is literally retained. -/
theorem pauliBobError_registeredExtension
    (ξ : H × K → ℂ) (a₀ : T) (projectPauli : PauliAnswer → ι → F)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    (p : PauliType) (q : κ → ZMod 2)
    (J : Option (ι → F) → Matrix (ι → F) (ι → F) ℂ) :
    (∑ z, snorm (registerState (ι → F) (extVecA ξ a₀)) (bOp
      ((((MB (QuestionType.pauli p, q)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (J z) : Matrix ((ι → F) × K) _ ℂ))) ^ 2) =
    ∑ z, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.pauli p, q)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (J z) : Matrix ((ι → F) × K) _ ℂ))) ^ 2 := by
  exact registeredExtension_bobSamePartyError ξ a₀ _
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem introBobZError_extVecA (projectPauli : PauliAnswer → ι → F) (Z : PauliType)
    (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) :
    introBobZError projectPauli Z q (extVecA ξ (none : Option ((ι → F) × A))) MB =
      introBobZError projectPauli Z q ξ MB :=
  pauliBobError_registeredExtension ξ none projectPauli MB Z q (readout some)
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveStageBudget_mono_depth {r s : ℕ} (hrs : r ≤ s)
    {e z h : ℝ} (he : 0 ≤ e) :
    adaptiveStageBudget r e z h ≤ adaptiveStageBudget s e z h := by
  have hrs' : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
  have hsquare : (r : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 := by
    nlinarith [(show (0 : ℝ) ≤ r from Nat.cast_nonneg r),
      (show (0 : ℝ) ≤ s from Nat.cast_nonneg s)]
  have hc : (512 * (r : ℝ) ^ 2 + 224) * e ≤
      (512 * (s : ℝ) ^ 2 + 224) * e :=
    mul_le_mul_of_nonneg_right (by linarith) he
  unfold adaptiveStageBudget
  linarith
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveStageBudget_mono_errors (r : ℕ)
    {e e' z z' h h' : ℝ} (he : e ≤ e') (hz : z ≤ z') (hh : h ≤ h') :
    adaptiveStageBudget r e z h ≤ adaptiveStageBudget r e' z' h' := by
  unfold adaptiveStageBudget
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (by norm_num))
    (mul_le_mul_of_nonneg_left he (by positivity)))
    (mul_le_mul_of_nonneg_left hh (by norm_num))
end
end MIPRE.Introspection

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
theorem adaptiveStageBudget_le_coefficient (r : ℕ) {edges f z h t : ℝ}
    (hE : 0 ≤ edges) (hf : f ≤ t) (hz : z ≤ t) (hh : h ≤ t) :
    adaptiveStageBudget r (edges * f) z h ≤ adaptiveBudgetCoefficient r edges * t := by
  calc
    _ ≤ adaptiveStageBudget r (edges * t) t t :=
      adaptiveStageBudget_mono_errors r (mul_le_mul_of_nonneg_left hf hE) hz hh
    _ = _ := by unfold adaptiveStageBudget adaptiveBudgetCoefficient; ring
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
/-- An explicit sufficient condition for every stage budget required by a
finite adaptive iteration, including the final numerical bound. -/
theorem adaptiveStageBudget_le_one_of_threshold (r N : ℕ) {edges z h initial : ℝ}
    (hE : 0 ≤ edges) (hi : initial ≤ adaptiveSmallThreshold r edges N)
    (hz : z ≤ adaptiveSmallThreshold r edges N)
    (hh : h ≤ adaptiveSmallThreshold r edges N)
    (n : ℕ) (hn : n ≤ N) :
    adaptiveStageBudget r (edges * adaptiveFailureBudget r edges z h initial n) z h ≤ 1 := by
  have hC := adaptiveBudgetCoefficient_pos r hE
  have ht₀ := adaptiveSmallThreshold_antitone r hE (Nat.zero_le N)
  have htn := adaptiveSmallThreshold_antitone r hE (Nat.zero_le (N - n))
  have hf := (adaptiveFailureBudget_le_threshold r N hE hi hz hh n hn).trans htn
  calc
    _ ≤ adaptiveBudgetCoefficient r edges * adaptiveSmallThreshold r edges 0 :=
      adaptiveStageBudget_le_coefficient r hE hf (hz.trans ht₀) (hh.trans ht₀)
    _ = 1 := by simp [adaptiveSmallThreshold, ne_of_gt hC]
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
variable {H Ω : Type u} {K : Type*}
  [Fintype H] [DecidableEq H] [Fintype Ω] [DecidableEq Ω]
  [Fintype K] [DecidableEq K]
variable {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
variable {PauliType PauliAnswer κ : Type*} {F ι A : Type u}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] {ℓ : ℕ}
/-- The primitive Bob-Z approximation is unchanged throughout the actual
Alice iteration, on the original EPR register and extended auxiliary state. -/
theorem introBobZError_introIterationState (projectPauli : PauliAnswer → ι → F)
    (Z : PauliType) (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (n : ℕ) :
    introBobZError projectPauli Z q
      (introIterationState ξ (none : Option ((ι → F) × A)) n) MB =
        introBobZError projectPauli Z q ξ MB := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (introBobZError_extVecA projectPauli Z q
        (introIterationState ξ (none : Option ((ι → F) × A)) n) MB).trans ih
end
end MIPRE.Introspection.TypedEstimates

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {H Ω : Type u} {K : Type*}
  [Fintype H] [DecidableEq H] [Fintype Ω] [DecidableEq Ω]
  [Fintype K] [DecidableEq K]
variable {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
variable {PauliType PauliAnswer κ : Type*} {F ι A : Type u}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] {ℓ : ℕ}
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
    (hZ : introBobZError projectPauli Z q ξ MB ≤ η)
    (hhide : ∀ j : Fin ℓ, hidingAliceError L w hL ξ MA j ≤ δ)
    (hi : initial ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hη : η ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hδ : δ ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (n : ℕ) (hn : n ≤ ℓ) :
    ∃ (MN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVM (ParsedAnswer (ι → F) A PauliAnswer)
          ((ι → F) × introIterationAux H (Option ((ι → F) × A)) n))
      (_ : IntroPrefixInvariant (L w) n
        ((MN (QuestionType.introspect w, 0)).map introspectPair)),
      (∀ t, IsPVM (fun a => ((MN t).mats a).val)) ∧
      1 - povmValue (parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F)
          (introIterationState ξ (none : Option ((ι → F) × A)) n)) MN MB ≤
            adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n ∧
      (∀ t, t ≠ (QuestionType.introspect w, 0) →
        MN t = introIterationExtend (Option ((ι → F) × A)) (MA t) n) ∧
      (∀ j : Fin ℓ, hidingAliceError L w hL
        (introIterationState ξ (none : Option ((ι → F) × A)) n) MN j =
          hidingAliceError L w hL ξ MA j) := by
  induction n with
  | zero =>
      refine ⟨MA, initialIntroPrefixInvariant (L w)
        ((MA (QuestionType.introspect w, 0)).map introspectPair)
        (isPVM_povm_map _ (hMA _) introspectPair), hMA, ?_, ?_, ?_⟩
      · exact hfail
      · intro t _
        rfl
      · intro j
        rfl
  | succ n ih =>
      have hn' : n ≤ ℓ := (Nat.le_succ n).trans hn
      obtain ⟨MN, IN, hMN, hfailN, hotherN, hhideN⟩ := ih hn'
      let j : Fin ℓ := ⟨n, by omega⟩
      have he : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
      have hb : 0 ≤ adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card
          η δ initial n :=
        adaptiveFailureBudget_nonneg ℓ n _ η δ hi0
      have hdepth : adaptiveStageBudget (ℓ - j.val)
          ((TypeGraph.edges E X Z ℓ).card *
            adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n) η δ ≤
          adaptiveStageBudget ℓ
            ((TypeGraph.edges E X Z ℓ).card *
              adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n) η δ :=
        adaptiveStageBudget_mono_depth (Nat.sub_le ℓ j.val) (mul_nonneg he hb)
      have hsmall := hdepth.trans
        (adaptiveStageBudget_le_one_of_threshold ℓ ℓ he hi hη hδ n hn')
      have hZn : introBobZError projectPauli Z q
          (introIterationState ξ (none : Option ((ι → F) × A)) n) MB ≤ η := by
        rw [introBobZError_introIterationState]
        exact hZ
      have hhn : hidingAliceError L w hL
          (introIterationState ξ (none : Option ((ι → F) × A)) n) MN j ≤ δ := by
        rw [hhideN j]
        exact hhide j
      obtain ⟨MS, IS, hMS, hfailS, hotherS, hhideS⟩ := exists_intro_successor
        E X Z P L projectPauli D DP
        (introIterationState ξ (none : Option ((ι → F) × A)) n)
        (introIterationState_unit ξ hξ none n) MN MB hMN hMB q hq w hL j IN
        hb hη0 hδ0 hfailN hZn hhn hsmall
      refine ⟨MS, IS, hMS, ?_, ?_, ?_⟩
      · exact hfailS.trans (by
          rw [adaptiveFailureBudget_step]
          exact add_le_add le_rfl (adaptiveStepLoss_mono hdepth))
      · intro t ht
        exact (hotherS t ht).trans (congrArg
          (fun N => registeredExtendPOVM (T := Option ((ι → F) × A)) N) (hotherN t ht))
      · intro i
        exact (hhideS i).trans (hhideN i)
end MIPRE.Introspection.TypedEstimates

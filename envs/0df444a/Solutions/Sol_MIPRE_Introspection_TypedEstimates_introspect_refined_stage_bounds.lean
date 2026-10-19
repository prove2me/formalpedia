-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.introspect_refined_stage_bounds
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:59:08.794081+00:00
-- url     : https://prove2.me/submissions/4097304e-b636-422d-9d2c-47c9716d88d3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveGameStage.lean (solution of MIPRE.Introspection.TypedEstimates.introspect_refined_stage_bounds);
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
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInduction
import Definitions.Def_MIPRE_Foundations_Introspection_HidingBaseOperators
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageZTests
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
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_introspect_adaptiveZ_commutator
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_introspect_adaptive_marginal
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_introspect_dual_commutator
import Theorems.Thm_MIPRE_Introspection_adaptiveX_reassembled_commutator_le
import Theorems.Thm_MIPRE_Introspection_norm_evec_comp_equiv
import Theorems.Thm_MIPRE_Introspection_prefixProjector_weight
import Theorems.Thm_MIPRE_Introspection_readout_isPVM
import Theorems.Thm_MIPRE_Introspection_registerEPR_equiv
import Theorems.Thm_MIPRE_Introspection_registerOp_kronecker
import Theorems.Thm_MIPRE_Introspection_registerOp_mulVec
import Theorems.Thm_MIPRE_Introspection_stateSqNorm_registerExtend
import Theorems.Thm_MIPRE_mulVec_kron_expVec
import Theorems.Thm_MIPRE_norm_evec_expVec

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
noncomputable section
open Finset Matrix
open scoped Kronecker
variable {V W H K : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- A product operator's squared state norm factors over a product state. -/
theorem stateSqNorm_expVec_kron (ψ : V × W → ℂ) (ξ : H × K → ℂ)
    (Q : Matrix V V ℂ) (A : Matrix H H ℂ) :
    stateSqNorm (expVec ψ ξ) (Q ⊗ₖ A) = stateSqNorm ψ Q * stateSqNorm ξ A := by
  unfold stateSqNorm stateNorm stateVec
  change ‖evec _‖ ^ 2 = ‖evec _‖ ^ 2 * ‖evec _‖ ^ 2
  rw [mulVec_kron_expVec, norm_evec_expVec, mul_pow]
end
end MIPRE.Introspection

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
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
/-- EPR on a product basis factors exactly into the two EPR states. -/
theorem registerEPR_prod :
    registerEPR (I × J) = expVec (registerEPR I) (registerEPR J) := by
  funext p
  obtain ⟨⟨i, j⟩, ⟨i', j'⟩⟩ := p
  simp only [registerEPR, expVec, Prod.mk.injEq, Fintype.card_prod, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), _root_.mul_inv_rev, Complex.ofReal_mul]
  by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [hi, hj, mul_comm]
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
/-- The EPR factorization under the actual party-wise register permutation. -/
theorem registerState_split (e : I ≃ J × R) (ξ : H × K → ℂ) :
    registerState I ξ =
      registerState J (registerState R ξ) ∘
        (registerParty e H).prodCongr (registerParty e K) := by
  have h := registerEPR_equiv e
  rw [registerEPR_prod] at h
  funext p
  have hp := congrFun h (p.1.1, p.2.1)
  change registerEPR I (p.1.1, p.2.1) * ξ (p.1.2, p.2.2) =
    registerEPR J ((e p.1.1).1, (e p.2.1).1) *
      (registerEPR R ((e p.1.1).2, (e p.2.1).2) * ξ (p.1.2, p.2.2))
  rw [← hp]
  exact mul_assoc _ _ _
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
/-- A local operator has exactly the same error in the split register presentation. -/
theorem stateSqNorm_registerState_split (e : I ≃ J × R) (ξ : H × K → ℂ)
    (M : Matrix (J × (R × H)) (J × (R × H)) ℂ) :
    stateSqNorm (registerState I ξ) (registerOp (registerParty e H) M) =
      stateSqNorm (registerState J (registerState R ξ)) M := by
  rw [registerState_split e ξ, stateSqNorm_registerOp]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem prefixResidualOp_sub (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M N : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    prefixResidualOp P k y (M - N) = prefixResidualOp P k y M - prefixResidualOp P k y N := by
  unfold prefixResidualOp
  ext i j
  simp only [registerOp_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply, mul_sub]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem prefixResidualOp_mul (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M N : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    prefixResidualOp P k y (M * N) = prefixResidualOp P k y M * prefixResidualOp P k y N := by
  unfold prefixResidualOp
  rw [← registerOp_mul, ← Matrix.mul_kronecker_mul]
  have hi : prefixProjector P k y * prefixProjector P k y = prefixProjector P k y :=
    (readout_isPVM _).idem y
  rw [hi]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
/-- Exact conditional error, on the concrete complement of the used prefix
register. It holds for every prefix, including impossible ones of weight zero. -/
theorem stateSqNorm_prefixResidualOp (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (ξ : H × K → ℂ)
    (M : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    stateSqNorm (registerState (ι → F) ξ) (prefixResidualOp P k y M) =
      prefixWeight P k y *
        stateSqNorm (registerState (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ξ) M := by
  rw [prefixResidualOp, stateSqNorm_registerState_split]
  change stateSqNorm
    (expVec (registerEPR (CLChecks.prefixRegister P k y → F))
      (registerState (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ξ))
    (prefixProjector P k y ⊗ₖ M) = _
  rw [stateSqNorm_expVec_kron, prefixProjector_weight P hP k y]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem prefixResidual_distance (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (ξ : H × K → ℂ)
    (M N : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    stateSqNorm (registerState (ι → F) ξ)
      (prefixResidualOp P k y M - prefixResidualOp P k y N) =
      prefixWeight P k y *
        stateSqNorm (registerState (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ξ) (M - N) := by
  rw [← prefixResidualOp_sub, stateSqNorm_prefixResidualOp P hP]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem prefixResidual_commutator (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (ξ : H × K → ℂ)
    (M N : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    stateSqNorm (registerState (ι → F) ξ)
      (prefixResidualOp P k y M * prefixResidualOp P k y N -
        prefixResidualOp P k y N * prefixResidualOp P k y M) =
      prefixWeight P k y *
        stateSqNorm (registerState (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ξ)
          (M * N - N * M) := by
  rw [← prefixResidualOp_mul, ← prefixResidualOp_mul, prefixResidual_distance P hP]
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
  [Fintype A] [DecidableEq A]
/-- Commutation on the ambient state is exactly commutation on the local EPR factor. -/
theorem ambientCommutatorError_eq (U V : Finset ι) (hUV : U ⊆ V) (ξ : H × K → ℂ)
    (M : (Fin (Fintype.card U) → F) × A → Matrix ((V → F) × H) ((V → F) × H) ℂ)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F)) :
    ambientCommutatorError U V hUV ξ M w L =
      registerCommutatorError (coordinateSplit U V hUV) ξ M w L := by
  unfold ambientCommutatorError registerCommutatorError ambientReadout ambientOperator
  simp_rw [← registerExtend_mul, ← registerExtend_sub, stateSqNorm_registerExtend]
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
theorem prefixStageCommutatorError_eq (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (w : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      Matrix (Fin (Fintype.card (P.factorOfPrefix k y)) → F) _ ℂ)
    (L : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →ₗ[F]
      (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) :
    prefixStageCommutatorError P hP k ξ M w L = ∑ y, prefixWeight P k y *
      ambientCommutatorError (P.factorOfPrefix k y) (stageRemaining P k y)
        (stageFactor_subset_remaining P hP k y) ξ (M y) (w y) (L y) := by
  simp only [prefixStageCommutatorError, prefixResidual_commutator P hP,
    ambientCommutatorError_eq, registerCommutatorError, stageSplit, Finset.mul_sum]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
theorem graphRefinement_sum_fun (M : A → Matrix D D ℂ) (c : A → C)
    (f : Matrix D D ℂ → ℝ) (hf : f 0 = 0) :
    (∑ p, f (graphRefinement M c p)) = ∑ a, f (M a) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [graphRefinement, apply_ite f, hf]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
theorem graphRefinement_eq_fibSum (M : A → Matrix D D ℂ) (c : A → C) (p : C × A) :
    graphRefinement M c p = fibSum M (fun a => (c a, a)) p := by
  rcases p with ⟨z, a⟩
  simp only [fibSum, Finset.sum_filter, Prod.mk.injEq]
  rw [Finset.sum_eq_single a]
  · simp [graphRefinement, eq_comm]
  · intro b _ hba
    simp [hba]
  · simp
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
theorem graphRefinementPOVM_mats (M : POVM A D) (c : A → C) (p : C × A) :
    ((graphRefinementPOVM M c).mats p).val =
      graphRefinement (fun a => (M.mats a).val) c p := by
  rw [graphRefinement_eq_fibSum]
  exact POVM.map_mats _ _ _
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
variable [Fintype K] [DecidableEq K] [Fintype B]
/-- Refinement introduces no commutator loss, for any comparison operators. -/
theorem graphRefinement_commutator_sum (ψ : D × K → ℂ) (M : A → Matrix D D ℂ)
    (c : A → C) (N : B → Matrix D D ℂ) :
    (∑ p, ∑ b, stateSqNorm ψ
      (graphRefinement M c p * N b - N b * graphRefinement M c p)) =
      ∑ a, ∑ b, stateSqNorm ψ (M a * N b - N b * M a) := by
  refine graphRefinement_sum_fun M c
    (fun Q => ∑ b, stateSqNorm ψ (Q * N b - N b * Q)) ?_
  simp [stateSqNorm, stateNorm, stateVec]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem stageAnswerRefinementPOVM_mats (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : POVM (Option ((ι → F) × A)) ((stageRemaining P k y → F) × H)) (p) :
    ((stageAnswerRefinementPOVM P k y M).mats p).val =
      stageAnswerRefinement P k y (fun a => (M.mats a).val) p :=
  graphRefinementPOVM_mats _ _ _
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
/-- Both the Z and dual-X local commutator budgets pass to the actual stage
alphabet exactly, including the malformed outcome. -/
theorem stageAnswerRefinement_commutator (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (ξ : H × K → ℂ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (w : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      Matrix (Fin (Fintype.card (P.factorOfPrefix k y)) → F) _ ℂ)
    (L : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →ₗ[F]
      (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) :
    prefixStageCommutatorError P hP k ξ (fun y => stageAnswerRefinement P k y (M y)) w L =
      ∑ y, prefixWeight P k y * ∑ a, ∑ z,
        stateSqNorm (registerState (stageRemaining P k y → F) ξ)
          (M y a * registerReadout (stageSplit P hP k y) (w y) (L y) z -
            registerReadout (stageSplit P hP k y) (w y) (L y) z * M y a) := by
  rw [prefixStageCommutatorError_eq]
  simp only [ambientCommutatorError_eq, registerCommutatorError]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact graphRefinement_commutator_sum _ _ _ _
end
end MIPRE.Introspection

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
variable {PauliType PauliAnswer κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] [Fintype A]
set_option maxHeartbeats 800000 in
/-- Actual parsed-game success and hiding rigidity supply the conditional
dual-X commutator estimate for the current adaptive product form. -/
theorem introspect_adaptiveX_commutator
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
    {ε δ : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (w : Bool) (hL : (L w).SupportedOn univ) (j : Fin ℓ)
    (hMA : IsPVM (fun a => ((MA (QuestionType.hide w j, 0)).mats a).val))
    (hMB : IsPVM (fun a => ((MB (QuestionType.read w, 0)).mats a).val))
    (hfine : ∑ i, xSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats i).val)
      (aOp (Honest.hideCoarseOp (L w) j.val hL i) : Matrix ((ι → F) × K) _ ℂ) ≤ δ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix ((stageRemaining (L w) j.val y → F) × H) _ ℂ)
    (hform : ∀ a, (((MA (QuestionType.introspect w, 0)).map introFullPair).mats a).val =
      ∑ y, prefixResidualOp (L w) j.val y (M y a)) :
    (∑ y, prefixWeight (L w) j.val y * ∑ a, ∑ z,
      stateSqNorm (registerState (stageRemaining (L w) j.val y → F) ξ)
        (M y a * registerReadout (stageSplit (L w) hL j.val y)
            wX (CL.lperp (coordinateLinear (CLChecks.stageLinear (L w) j.val y))) z -
          registerReadout (stageSplit (L w) hL j.val y)
            wX (CL.lperp (coordinateLinear (CLChecks.stageLinear (L w) j.val y))) z * M y a)) ≤
      16 * ((32 * ((ℓ - j.val : ℕ) : ℝ) ^ 2 + 6) *
        (TypeGraph.edges E X Z ℓ).card * ε + 4 * δ) := by
  have ht := introspect_dual_commutator E X Z P L projectPauli D DP
    ξ hξ MA MB hfail w hL j hMA hMB hfine
  apply (adaptiveX_reassembled_commutator_le (L w) hL j.val ξ M).trans
  simpa only [hform] using ht
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection
section
theorem marginal_le_adaptiveStageBudget (r : ℕ) {e z h : ℝ}
    (he : 0 ≤ e) (hz : 0 ≤ z) (hh : 0 ≤ h) :
    16 * z + 56 * e ≤ adaptiveStageBudget r e z h := by
  unfold adaptiveStageBudget
  nlinarith [mul_nonneg (sq_nonneg (r : ℝ)) he]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
section
theorem Z_le_adaptiveStageBudget (r : ℕ) {e z h : ℝ}
    (he : 0 ≤ e) (hh : 0 ≤ h) :
    64 * z + 224 * e ≤ adaptiveStageBudget r e z h := by
  unfold adaptiveStageBudget
  nlinarith [mul_nonneg (sq_nonneg (r : ℝ)) he]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
section
theorem X_le_adaptiveStageBudget (r : ℕ) {e z h : ℝ}
    (he : 0 ≤ e) (hz : 0 ≤ z) :
    16 * ((32 * (r : ℝ) ^ 2 + 6) * e + 4 * h) ≤
      adaptiveStageBudget r e z h := by
  unfold adaptiveStageBudget
  nlinarith
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
theorem _root_.solution :
    let budget := adaptiveStageBudget (ℓ - j.val)
      ((TypeGraph.edges E X Z ℓ).card * ε) η δ
    let R := fun y p => ((stageAnswerRefinementPOVM (L w) j.val y (M y)).mats p).val
    prefixStageMarginalError (L w) hL j.val ξ R ≤ budget ∧
    prefixStageCommutatorError (L w) hL j.val ξ R
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ budget ∧
    prefixStageCommutatorError (L w) hL j.val ξ R
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear (L w) j.val y)))
      ≤ budget := by
  dsimp only
  simp only [stageAnswerRefinementPOVM_mats]
  have he : 0 ≤ (TypeGraph.edges E X Z ℓ).card * ε := mul_nonneg (Nat.cast_nonneg _) hε
  have hm := introspect_adaptive_marginal E X Z P L projectPauli D DP ξ hξ MA MB
    hfail q hq w hL hSA hZ j.val (fun y a => ((M y).mats a).val) hform hsupport
  have hz := introspect_adaptiveZ_commutator E X Z P L projectPauli D DP ξ hξ MA MB
    hfail q hq w hSB hZ hL j.val (fun y a => ((M y).mats a).val) hform
  have hx := introspect_adaptiveX_commutator E X Z P L projectPauli D DP ξ hξ MA MB
    hfail w hL j hHide hRead hfine (fun y a => ((M y).mats a).val) hform
  refine ⟨hm.trans ?_, ?_, ?_⟩
  · simpa only [mul_assoc] using marginal_le_adaptiveStageBudget (ℓ - j.val) he hη hδ
  · rw [stageAnswerRefinement_commutator]
    apply hz.trans
    simpa only [mul_assoc] using
      (Z_le_adaptiveStageBudget (z := η) (ℓ - j.val) he hδ)
  · rw [stageAnswerRefinement_commutator]
    apply hx.trans
    simpa only [mul_assoc] using
      (X_le_adaptiveStageBudget (h := δ) (ℓ - j.val) he hη)
end MIPRE.Introspection.TypedEstimates

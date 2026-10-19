-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.introspect_adaptiveZ_commutator
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:56:07.558427+00:00
-- url     : https://prove2.me/submissions/12dca0f7-a2da-43a3-918f-eb879724ad9f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveZTest.lean (solution of MIPRE.Introspection.TypedEstimates.introspect_adaptiveZ_commutator);
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
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
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
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveZFactor
import Definitions.Def_MIPRE_Foundations_Introspection_PauliAuxEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingRegister
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInduction
import Definitions.Def_MIPRE_Foundations_Introspection_HidingBaseOperators
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageZTests
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_introspect_coarseZ_commutator_alice
import Theorems.Thm_MIPRE_Introspection_adaptiveZ_readout_factor
import Theorems.Thm_MIPRE_Introspection_norm_evec_comp_equiv
import Theorems.Thm_MIPRE_Introspection_prefixProjector_weight
import Theorems.Thm_MIPRE_Introspection_prefixResidual_reassembled_commutator
import Theorems.Thm_MIPRE_Introspection_registerEPR_equiv
import Theorems.Thm_MIPRE_Introspection_registerOp_kronecker
import Theorems.Thm_MIPRE_Introspection_registerOp_mulVec
import Theorems.Thm_MIPRE_aOp_zero
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
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
/-- The global commutation error equals the actual prefix-weighted local
commutation error, even when ideal outcome types depend on the prefix. -/
theorem prefixResidual_reassembled_commutator_sum (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (ξ : H × K → ℂ)
    {A : Type*} [Fintype A] {B : (ι → F) → Type*} [∀ y, Fintype (B y)]
    (M : (y : ι → F) → A → Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (N : (y : ι → F) → B y → Matrix ((stageRemaining P k y → F) × H) _ ℂ) :
    (∑ a, ∑ p : (y : ι → F) × B y, stateSqNorm (registerState (ι → F) ξ)
      ((∑ z, prefixResidualOp P k z (M z a)) * prefixResidualOp P k p.1 (N p.1 p.2) -
        prefixResidualOp P k p.1 (N p.1 p.2) * (∑ z, prefixResidualOp P k z (M z a)))) =
      ∑ y, prefixWeight P k y * ∑ a, ∑ b,
        stateSqNorm (registerState (stageRemaining P k y → F) ξ)
          (M y a * N y b - N y b * M y a) := by
  simp only [Fintype.sum_sigma, prefixResidual_reassembled_commutator P hP,
    stateSqNorm_prefixResidualOp P hP]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
/-- Specialization to the actual seed coarse-graining which records the CL
prefix and its next Z coordinates. This is the tested global coarse Z family,
not an independently supplied collection of prefix-local ideals. -/
theorem adaptiveZ_reassembled_commutator_sum (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (ξ : H × K → ℂ)
    {A : Type*} [Fintype A]
    (M : (y : ι → F) → A → Matrix ((stageRemaining P k y → F) × H) _ ℂ) :
    (∑ a, ∑ p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F),
      stateSqNorm (registerState (ι → F) ξ)
        ((∑ z, prefixResidualOp P k z (M z a)) *
            (aOp (readout (adaptiveZOutcome P k) p) : Matrix ((ι → F) × H) _ ℂ) -
          (aOp (readout (adaptiveZOutcome P k) p) : Matrix ((ι → F) × H) _ ℂ) *
            (∑ z, prefixResidualOp P k z (M z a)))) =
      ∑ y, prefixWeight P k y * ∑ a, ∑ z,
        stateSqNorm (registerState (stageRemaining P k y → F) ξ)
          (M y a * registerReadout (stageSplit P hP k y) wZ LinearMap.id z -
            registerReadout (stageSplit P hP k y) wZ LinearMap.id z * M y a) := by
  have hf (p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) :
      (aOp (readout (adaptiveZOutcome P k) p) : Matrix ((ι → F) × H) _ ℂ) =
        prefixResidualOp P k p.1
          (registerReadout (stageSplit P hP k p.1) wZ LinearMap.id p.2) :=
    adaptiveZ_readout_factor P hP k p.1 p.2
  simp_rw [hf]
  exact prefixResidual_reassembled_commutator_sum
    (B := fun y => Fin (Fintype.card (P.factorOfPrefix k y)) → F) P hP k ξ M
    (fun y z => registerReadout (H := H) (stageSplit P hP k y) wZ LinearMap.id z)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
theorem readout_some_comp {I C : Type*} [Fintype I] [DecidableEq I]
    [Fintype C] [DecidableEq C] (g : I → C) (c : C) :
    readout (fun i => some (g i)) (some c) = readout g c := by
  ext i j
  simp [readout]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
theorem readout_none_comp {I C : Type*} [Fintype I] [DecidableEq I]
    [Fintype C] [DecidableEq C] (g : I → C) :
    readout (fun i => some (g i)) none = 0 := by
  ext i j
  simp [readout]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
/-- The impossible `none` ideal contributes zero, without splitting the
actual measurement's outcome alphabet. -/
theorem option_readout_commutator_sum {I C H K B : Type*}
    [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C]
    [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] [Fintype B]
    (ψ : (I × H) × K → ℂ) (g : I → C)
    (M : B → Matrix (I × H) (I × H) ℂ) :
    (∑ b, ∑ c : Option C, stateSqNorm ψ
      (M b * aOp (readout (fun i => some (g i)) c) -
        aOp (readout (fun i => some (g i)) c) * M b)) =
    ∑ b, ∑ c : C, stateSqNorm ψ
      (M b * aOp (readout g c) - aOp (readout g c) * M b) := by
  have hz : stateSqNorm ψ (0 : Matrix (I × H) (I × H) ℂ) = 0 := by
    simp [stateSqNorm, stateNorm, stateVec]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.sum_option]
  simp only [readout_none_comp, readout_some_comp, aOp_zero,
    mul_zero, zero_mul, sub_self, hz, zero_add]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] {ℓ : ℕ}
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
    {ε η : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q) (w : Bool)
    (hS : IsPVM (fun a => ((MB (QuestionType.sample w, 0)).mats a).val))
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ η)
    (hL : (L w).SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix ((stageRemaining (L w) k y → F) × H) _ ℂ)
    (hform : ∀ a, (((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val =
      ∑ y, prefixResidualOp (L w) k y (M y a)) :
    (∑ y, prefixWeight (L w) k y * ∑ a, ∑ z,
      stateSqNorm (registerState (stageRemaining (L w) k y → F) ξ)
        (M y a * registerReadout (stageSplit (L w) hL k y) wZ LinearMap.id z -
          registerReadout (stageSplit (L w) hL k y) wZ LinearMap.id z * M y a)) ≤
      64 * η + 224 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have ht := introspect_coarseZ_commutator_alice E X Z P L projectPauli D DP
    ξ hξ MA MB hfail q hq w hS hZ (adaptiveZOutcome (L w) k)
  have he := option_readout_commutator_sum (registerState (ι → F) ξ)
    (adaptiveZOutcome (L w) k)
    (fun a => (((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val)
  have hbound := he.symm.trans_le ht
  have hg := adaptiveZ_reassembled_commutator_sum (L w) hL k ξ M
  apply hg.symm.trans_le
  calc
    _ = ∑ a, ∑ c, stateSqNorm (registerState (ι → F) ξ)
        ((((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val *
            (aOp (readout (adaptiveZOutcome (L w) k) c) : Matrix ((ι → F) × H) _ ℂ) -
          (aOp (readout (adaptiveZOutcome (L w) k) c) : Matrix ((ι → F) × H) _ ℂ) *
            (((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      rw [hform a]
    _ ≤ _ := hbound
end MIPRE.Introspection.TypedEstimates

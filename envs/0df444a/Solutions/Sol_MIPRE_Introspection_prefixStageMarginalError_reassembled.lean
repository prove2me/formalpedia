-- Prove2me | solution 1 for MIPRE.Introspection.prefixStageMarginalError_reassembled
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:48:39.008005+00:00
-- url     : https://prove2.me/submissions/c72c8f75-e34c-4c0d-a1ad-9e0da8ce7363

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptivePrefixMarginal.lean (solution of MIPRE.Introspection.prefixStageMarginalError_reassembled);
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
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveZFactor
import Definitions.Def_MIPRE_Foundations_Introspection_PauliAuxEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixAdvance
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMarginal
import Theorems.Thm_MIPRE_Introspection_adaptiveLinear_readout_factor
import Theorems.Thm_MIPRE_Introspection_advancePrefix_eval
import Theorems.Thm_MIPRE_Introspection_advancePrefix_fibSum_sqNorm
import Theorems.Thm_MIPRE_aOp_sum

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {V H I Y Z : Type*}
  [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]
theorem fibSum_aOp (P : I → Matrix V V ℂ) (f : I → Z) (z : Z) :
    fibSum (fun i => (aOp (P i) : Matrix (V × H) _ ℂ)) f z = aOp (fibSum P f z) :=
  (aOp_sum _ _).symm
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
/-- Coarse-graining a computational readout reads the composite function. -/
theorem fibSum_readout {I Y Z : Type*} [Fintype I] [DecidableEq I]
    [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (f : I → Y) (g : Y → Z) (z : Z) :
    fibSum (readout f) g z = readout (g ∘ f) z := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [fibSum, readout, Matrix.sum_apply, eq_comm]
  · simp [fibSum, readout, Matrix.sum_apply, hij]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F]
theorem advancePrefix_adaptiveLinearOutcome {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (x : ι → F) :
    advancePrefix P k (adaptiveLinearOutcome P k x).1 (adaptiveLinearOutcome P k x).2 =
      (P.truncate (k + 1)).eval x := advancePrefix_eval hP k x
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F]
/-- The next prefix readout is exactly the coarse-graining of the old prefix
and current linear readout under the concrete next-label map. -/
theorem advancePrefix_readout {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (v : ι → F) :
    readout (P.truncate (k + 1)).eval v =
      fibSum (readout (adaptiveLinearOutcome P k))
        (fun p => advancePrefix P k p.1 p.2) v := by
  rw [fibSum_readout]
  congr 1
  funext x
  exact (advancePrefix_adaptiveLinearOutcome hP k x).symm
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F]
variable [Algebra (ZMod 2) F] {H : Type*} [Fintype H] [DecidableEq H]
/-- Reassembling old-prefix/current-linear projectors by the advanced label
gives exactly the next honest prefix measurement. -/
theorem advancePrefix_projector_assembly (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (v : ι → F) :
    (aOp (Honest.hidingPrefixOp P (k + 1) (some v)) : Matrix ((ι → F) × H) _ ℂ) =
      fibSum
        (fun p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F) =>
          prefixResidualOp P k p.1 (registerReadout (stageSplit P hP k p.1) wZ
            (coordinateLinear (CLChecks.stageLinear P k p.1)) p.2))
        (fun p => advancePrefix P k p.1 p.2) v := by
  rw [Honest.hidingPrefixOp_some, advancePrefix_readout hP, ← fibSum_aOp]
  apply Finset.sum_congr rfl
  intro p _
  exact adaptiveLinear_readout_factor P hP k p.1 p.2
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Weyl Classical
set_option linter.unusedSectionVars false
variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem _root_.solution (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (ξ : H × K → ℂ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix ((stageRemaining P k y → F) × H) ((stageRemaining P k y → F) × H) ℂ) :
    prefixStageMarginalError P hP k ξ M =
      ∑ v, stateSqNorm (registerState (ι → F) ξ)
        (fibSum
          (fun p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F) =>
            prefixResidualOp P k p.1 (∑ a, M p.1 (p.2, a)))
          (fun p => advancePrefix P k p.1 p.2) v -
          aOp (Honest.hidingPrefixOp P (k + 1) (some v))) := by
  have hh := advancePrefix_fibSum_sqNorm P hP k (registerState (ι → F) ξ)
    (fun p => (∑ a, M p.1 (p.2, a)) -
      registerReadout (stageSplit P hP k p.1) wZ
        (coordinateLinear (CLChecks.stageLinear P k p.1)) p.2)
  simp only [prefixResidualOp_sub, fibSum, Finset.sum_sub_distrib,
    Fintype.sum_sigma] at hh
  unfold prefixStageMarginalError
  rw [← hh]
  apply Finset.sum_congr rfl
  intro v _
  rw [advancePrefix_projector_assembly P hP k v]
  rfl
end MIPRE.Introspection

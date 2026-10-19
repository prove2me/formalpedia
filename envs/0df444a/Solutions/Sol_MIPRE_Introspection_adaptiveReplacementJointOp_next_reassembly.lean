-- Prove2me | solution 1 for MIPRE.Introspection.adaptiveReplacementJointOp_next_reassembly
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:51:12.425647+00:00
-- url     : https://prove2.me/submissions/8c49e654-2d7a-4803-8a64-f147bfaea97e

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveNextInvariant.lean (solution of MIPRE.Introspection.adaptiveReplacementJointOp_next_reassembly);
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
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveZFactor
import Definitions.Def_MIPRE_Foundations_Introspection_PauliAuxEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixAdvance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacementRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDilationTransport
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextFactor
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextInvariant
import Theorems.Thm_MIPRE_Introspection_adaptiveReplacementJointOp_next_factor
import Theorems.Thm_MIPRE_Introspection_advancePrefix_injective

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
theorem prefixProjector_eq_zero (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (hy : y ∉ prefixOutcomes P k) : prefixProjector P k y = 0 := by
  have hf (u : CLChecks.prefixRegister P k y → F) :
      (P.truncate k).eval (insertRegister (CLChecks.prefixRegister P k y) u) ≠ y := by
    intro he
    apply hy
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, he⟩
  ext i j
  simp [prefixProjector, readout, hf]
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
theorem prefixResidualOp_eq_zero (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (hy : y ∉ prefixOutcomes P k)
    (M : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    prefixResidualOp P k y M = 0 := by
  unfold prefixResidualOp
  rw [prefixProjector_eq_zero P k y hy]
  ext i j
  simp [registerOp_apply]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem prefixResidualOp_nextResidualOpAt (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F)
    (v : ι → F) (hv : advancePrefix P k y z = v)
    (N : Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) _ ℂ) :
    prefixResidualOp P (k + 1) (advancePrefix P k y z) (nextResidualOp P hP k y z N) =
      prefixResidualOp P (k + 1) v (nextResidualOpAt P hP k y z v hv N) := by
  subst v
  rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem adaptiveReplacementJointOp_off_prefix (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (D : AdaptiveDilationFamily P k H A)
    (p : AdaptiveStageAnswer P k A) (hp : p.1 ∉ prefixOutcomes P k) :
    adaptiveReplacementJointOp P hP k D p = 0 :=
  prefixResidualOp_eq_zero P k p.1 hp _
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem adaptiveReplacementJointOp_off_next (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (D : AdaptiveDilationFamily P k H A)
    (p : AdaptiveStageAnswer P k A)
    (hp : (advanceStageAnswer P k p).1 ∉ prefixOutcomes P (k + 1)) :
    adaptiveReplacementJointOp P hP k D p = 0 := by
  by_cases hy : p.1 ∈ prefixOutcomes P k
  · rw [adaptiveReplacementJointOp_next_factor P hP k D p.1 hy]
    exact prefixResidualOp_eq_zero P (k + 1) _ hp _
  · exact adaptiveReplacementJointOp_off_prefix P hP k D p hy
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem advanceStageAnswer_injective_support (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (p q : AdaptiveStageAnswer P k A) (hp : p.1 ∈ prefixOutcomes P k)
    (hq : q.1 ∈ prefixOutcomes P k)
    (he : advanceStageAnswer P k p = advanceStageAnswer P k q) : p = q := by
  have hcoord := advancePrefix_injective hP k
    (a₁ := ⟨⟨p.1, hp⟩, p.2.1⟩) (a₂ := ⟨⟨q.1, hq⟩, q.2.1⟩) (congrArg Prod.fst he)
  have ha : p.2.2 = q.2.2 := congrArg Prod.snd he
  cases p with | mk y p =>
    cases q with | mk y' q =>
      have hy : y = y' := congrArg (fun r : AttainableStageCoordinate P k => r.1.val) hcoord
      subst y'
      have hz : p.1 = q.1 := by
        have hh := Sigma.mk.inj_iff.mp hcoord
        exact eq_of_heq hh.2
      exact congrArg (Sigma.mk y) (Prod.ext hz ha)
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem _root_.solution (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (a₀ : A)
    (D : AdaptiveDilationFamily P k H A) (v : ι → F) (a : A) :
    fibSum (adaptiveReplacementJointOp P hP k D) (advanceStageAnswer P k) (v, a) =
      prefixResidualOp P (k + 1) v (nextPrefixResidual P hP k a₀ D v a) := by
  by_cases hv : v ∈ prefixOutcomes P (k + 1)
  · let p := nextPrefixSource P hP k v hv
    let q : AdaptiveStageAnswer P k A := ⟨p.1, (p.2, a)⟩
    have hq : advanceStageAnswer P k q = (v, a) :=
      Prod.ext (nextPrefixSource_advance P hP k v hv) rfl
    have hm : q ∈ univ.filter (fun r => advanceStageAnswer P k r = (v, a)) := by simp [hq]
    have heq : fibSum (adaptiveReplacementJointOp P hP k D) (advanceStageAnswer P k) (v, a) =
        adaptiveReplacementJointOp P hP k D q := by
      apply Finset.sum_eq_single_of_mem q hm
      intro r hr hrq
      apply adaptiveReplacementJointOp_off_prefix P hP k D r
      intro hrg
      exact hrq (advanceStageAnswer_injective_support P hP k r q hrg p.1.property
        ((mem_filter.mp hr).2.trans hq.symm))
    rw [heq]
    change adaptiveReplacementJointOp P hP k D ⟨p.1.val, (p.2, a)⟩ = _
    rw [adaptiveReplacementJointOp_next_factor P hP k D p.1 p.1.property]
    have hp := nextPrefixSource_advance P hP k v hv
    change prefixResidualOp P (k + 1) (advancePrefix P k p.1 p.2)
      (nextResidualOp P hP k p.1 p.2 (D p.1 p.2 a)) = _
    simp only [nextPrefixResidual, dif_pos hv]
    exact prefixResidualOp_nextResidualOpAt P hP k p.1 p.2 v hp _
  · rw [prefixResidualOp_eq_zero P (k + 1) v hv]
    apply Finset.sum_eq_zero
    intro p hp
    apply adaptiveReplacementJointOp_off_next P hP k D p
    have he : (advanceStageAnswer P k p).1 = v := congrArg Prod.fst (mem_filter.mp hp).2
    simpa only [he] using hv
end MIPRE.Introspection

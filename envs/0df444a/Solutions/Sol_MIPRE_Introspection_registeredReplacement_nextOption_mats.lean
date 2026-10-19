-- Prove2me | solution 1 for MIPRE.Introspection.registeredReplacement_nextOption_mats
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:28:07.651426+00:00
-- url     : https://prove2.me/submissions/0499a004-1cf3-4a63-9770-55d41d1d81c6

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveDecodedInvariant.lean (solution of MIPRE.Introspection.registeredReplacement_nextOption_mats);
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
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextFactor
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextStrategy
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInduction
import Definitions.Def_MIPRE_Foundations_Introspection_HidingBaseOperators
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageZTests
import Definitions.Def_MIPRE_Foundations_Introspection_IntrospectCanonicalization
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDecodedInvariant
import Theorems.Thm_MIPRE_Introspection_adaptiveReplacementJointOp_next_reassembly
import Theorems.Thm_MIPRE_Introspection_nextPrefixJointPOVM_map_mats
import Theorems.Thm_MIPRE_POVM_map_map
import Theorems.Thm_MIPRE_POVM_map_reindex

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

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
/-- Returning from the extension ordering reveals exactly the prefix and
new Z-factor measurement constructed on the new auxiliary space. -/
theorem adaptiveReplacementPOVM_reindex (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z)) :
    (adaptiveReplacementPOVM P hP k D hD).reindex (Equiv.prodAssoc (ι → F) H A) =
      (adaptiveReplacementJointOp_isPVM P hP k D hD).toPOVM := by
  apply POVM.ext'
  intro p
  change registerOp (Equiv.prodAssoc (ι → F) H A).symm
    (registerOp (Equiv.prodAssoc (ι → F) H A) (adaptiveReplacementJointOp P hP k D p)) = _
  exact registerOp_inv _ _
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
/-- After coordinate reassociation, the actual replacement measurement is
exactly the constructed next-prefix PVM with its answer retained. -/
theorem adaptiveReplacementPOVM_next (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k H A)
    (hD : ∀ y z, IsPVM (D y z)) :
    ((adaptiveReplacementPOVM P hP k D hD).reindex (Equiv.prodAssoc (ι → F) H A)).map
      (advanceStageAnswer P k) = nextPrefixJointPOVM P hP k a₀ D hD := by
  rw [adaptiveReplacementPOVM_reindex]
  apply POVM.ext'
  intro p
  rw [POVM.map_mats]
  change fibSum (adaptiveReplacementJointOp P hP k D) (advanceStageAnswer P k) p = _
  exact adaptiveReplacementJointOp_next_reassembly P hP k a₀ D p.1 p.2
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
variable {X Y Ans B : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype Ans] [DecidableEq Ans] [Fintype B] [DecidableEq B]
/-- Decoding the retained answer commutes with advancing the concrete
replacement into its next-prefix residual form. -/
theorem adaptiveReplacementPOVM_next_decode (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (a₀ : A)
    (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z))
    (g : (ι → F) × A → Ans) :
    ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => g (advanceStageAnswer P k p))).reindex (Equiv.prodAssoc (ι → F) H A) =
      (nextPrefixJointPOVM P hP k a₀ D hD).map g := by
  rw [POVM.map_reindex, ← POVM.map_map _ (advanceStageAnswer P k) g,
    adaptiveReplacementPOVM_next]
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
variable {X Y Ans B : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype Ans] [DecidableEq Ans] [Fintype B] [DecidableEq B]
/-- The actual question-indexed strategy family has the constructed next
form at the selected question; the other questions are still supplied by
the existing registered replacement constructor. -/
theorem registeredReplacement_next_at (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (a₀ : A)
    (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z))
    (MA : X → POVM Ans ((ι → F) × H)) (q : X) (g : (ι → F) × A → Ans) :
    registeredReplacement MA q ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => g (advanceStageAnswer P k p))) q =
        (nextPrefixJointPOVM P hP k a₀ D hD).map g := by
  rw [registeredReplacement_at, adaptiveReplacementPOVM_next_decode]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable {X PauliAnswer : Type*} [Fintype X] [DecidableEq X] [Fintype PauliAnswer]
/-- Projecting the actual raw selected replacement recovers exactly the
canonical option-valued next joint measurement. -/
theorem registeredReplacement_nextOption_at (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (D : AdaptiveDilationFamily P k H (Option ((ι → F) × A)))
    (hD : ∀ y z, IsPVM (D y z))
    (MA : X → POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (q : X) :
    (registeredReplacement MA q ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => restoreIntroAnswer (nextOptionDecoder P k (advanceStageAnswer P k p)))) q).map
        TypedEstimates.introspectPair =
      (nextPrefixJointPOVM P hP k none D hD).map (nextOptionDecoder P k) := by
  rw [registeredReplacement_next_at P hP k none D hD MA q
    (fun p => restoreIntroAnswer (nextOptionDecoder P k p)), POVM.map_map]
  simp only [introspectPair_restoreIntroAnswer]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable {X PauliAnswer : Type*} [Fintype X] [DecidableEq X] [Fintype PauliAnswer]
theorem _root_.solution (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (D : AdaptiveDilationFamily P k H (Option ((ι → F) × A)))
    (hD : ∀ y z, IsPVM (D y z))
    (MA : X → POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (q : X)
    (a : Option ((ι → F) × A)) :
    (((registeredReplacement MA q ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => restoreIntroAnswer (nextOptionDecoder P k (advanceStageAnswer P k p)))) q).map
        TypedEstimates.introspectPair).mats a).val =
      ∑ v, prefixResidualOp P (k + 1) v
        ((nextPrefixDecodedPOVM P hP k none D hD (nextOptionDecoder P k) v).mats a).val := by
  rw [registeredReplacement_nextOption_at P hP k D hD MA q]
  exact nextPrefixJointPOVM_map_mats P hP k none D hD (nextOptionDecoder P k) a
end MIPRE.Introspection

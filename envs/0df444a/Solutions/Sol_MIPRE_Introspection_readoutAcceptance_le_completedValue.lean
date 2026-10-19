-- Prove2me | solution 1 for MIPRE.Introspection.readoutAcceptance_le_completedValue
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:31:26.05405+00:00
-- url     : https://prove2.me/submissions/66a4a0bf-723f-41b0-a44a-173c7e3106ae

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TerminalOptionExtraction.lean (solution of MIPRE.Introspection.readoutAcceptance_le_completedValue);
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
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveTerminalInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_TerminalOptionExtraction
import Theorems.Thm_MIPRE_Introspection_bornProb_registerEPR_readout
import Theorems.Thm_MIPRE_Introspection_option_valid_acceptance_le_complete
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_mulVec_kron_kron_expVec

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
/-- A product of sums as a sum over the product. -/
theorem sum_prod_mul {X Y M : Type*} [Fintype X] [Fintype Y] [CommRing M] (f : X → M)
    (g : Y → M) : ∑ q : X × Y, f q.1 * g q.2 = (∑ x, f x) * ∑ y, g y := by
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
theorem expVec_dotProduct_of_pair (u u' : dA × dB → ℂ) (v v' : anc × anc' → ℂ) :
    star (expVec u v) ⬝ᵥ expVec u' v' = (star u ⬝ᵥ u') * (star v ⬝ᵥ v') := by
  classical
  rw [dotProduct, dotProduct, dotProduct, ← sum_prod_mul]
  refine Fintype.sum_equiv (expEquiv dA dB anc anc') _ _ fun p => ?_
  obtain ⟨⟨a, x⟩, ⟨b, y⟩⟩ := p
  simp only [expEquiv, Equiv.coe_fn_mk, Pi.star_apply, expVec, star_mul']
  ring
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
/-- **The Born probability of a product measurement on the expanded state factorizes.** Only the
ancilla's two operators need to be positive: that is what makes their quadratic form real, which is
what lets the real part of the product split. -/
theorem bornProb_expVec_kron (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) {X : Matrix dA dA ℂ}
    {Y : Matrix anc anc ℂ} {X' : Matrix dB dB ℂ} {Y' : Matrix anc' anc' ℂ}
    (hY : Y.PosSemidef) (hY' : Y'.PosSemidef) :
    bornProb (expVec ψ e) (X ⊗ₖ Y) (X' ⊗ₖ Y') = bornProb ψ X X' * bornProb e Y Y' := by
  have hre : ∀ (Z : Matrix (anc × anc') (anc × anc') ℂ), Z.PosSemidef →
      (star e ⬝ᵥ (Z *ᵥ e)).im = 0 :=
    fun Z hZ => ((Complex.nonneg_iff.mp (hZ.dotProduct_mulVec_nonneg e)).2).symm
  rw [bornProb, mulVec_kron_kron_expVec, expVec_dotProduct_of_pair, bornProb, bornProb,
    Complex.mul_re, hre _ (hY.kronecker hY'), mul_zero, sub_zero]
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {I X Y A B H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
/-- The full joint answer probability factors into the original question law and
the auxiliary strategy's conditional answer probability. -/
theorem bornProb_conditionalReadout (f : I → X) (g : I → Y) (ξ : H × K → ℂ)
    (P : X → A → Matrix H H ℂ) (Q : Y → B → Matrix K K ℂ)
    (hP : ∀ x a, (P x a).PosSemidef) (hQ : ∀ y b, (Q y b).PosSemidef)
    (xa : X × A) (yb : Y × B) :
    bornProb (registerState I ξ) (conditionalReadout f P xa) (conditionalReadout g Q yb) =
      SampledGame.dist f g xa.1 yb.1 * bornProb ξ (P xa.1 xa.2) (Q yb.1 yb.2) := by
  rw [registerState, conditionalReadout, conditionalReadout,
    bornProb_expVec_kron _ _ (hP _ _) (hQ _ _), bornProb_registerEPR_readout]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I X Y A B H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
theorem _root_.solution (G : Game X Y A B)
    (f : I → X) (g : I → Y)
    (hμ : ∀ x y, G.μ x y = SampledGame.dist f g x y)
    (ξ : H × K → ℂ) (Q : X → POVM (Option A) H) (R : Y → POVM (Option B) K)
    (a₀ : A) (b₀ : B) :
    readoutAcceptance f g ξ (fun x a => ((Q x).mats (some a)).val)
      (fun y b => ((R y).mats (some b)).val) G.D ≤
        povmValue G ξ (fun x => completeOptionPOVM a₀ (Q x))
          (fun y => completeOptionPOVM b₀ (R y)) := by
  have he : readoutAcceptance f g ξ (fun x a => ((Q x).mats (some a)).val)
      (fun y b => ((R y).mats (some b)).val) G.D =
      ∑ x, ∑ y, G.μ x y * ∑ a, ∑ b, (if G.D x y a b then (1 : ℝ) else 0) *
        bornProb ξ ((Q x).mats (some a)).val ((R y).mats (some b)).val := by
    unfold readoutAcceptance
    simp_rw [bornProb_conditionalReadout f g ξ _ _
      (fun x a => (Q x).posSemidef (some a))
      (fun y b => (R y).posSemidef (some b))]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hμ]
    ring
  rw [he]
  unfold povmValue condWin
  exact Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ =>
    mul_le_mul_of_nonneg_left
      (option_valid_acceptance_le_complete ξ (Q x) (R y) a₀ b₀ (G.D x y))
      (G.μ_nonneg x y)))
end MIPRE.Introspection

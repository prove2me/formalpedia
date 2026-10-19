-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_valid_isometric_images
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T07:11:32.103637+00:00
-- url     : https://prove2.me/submissions/012ab954-296d-496e-8a0c-12523f249234

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ValidPauliSoundness.lean (solution of MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_valid_isometric_images);
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
import Definitions.Def_MIPRE_Foundations_Introspection_ValidPauliSoundness
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_quantumValue_ge_of_isometric_images
import Theorems.Thm_MIPRE_Introspection_isometric_valid_outcome_alice_error_le
import Theorems.Thm_MIPRE_Introspection_isometric_valid_outcome_bob_error_le
import Theorems.Thm_MIPRE_Introspection_readout_isPVM
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_Weyl_isPVM_synOf
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wX
import Theorems.Thm_MIPRE_aOp_zero
import Theorems.Thm_MIPRE_norm_evec_expVec

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem pauliXReadout_isPVM : IsPVM (pauliXReadout (F := F) (ι := ι)) :=
  isPVM_synOf isWeylFamily_wX some
end
end MIPRE.Introspection.Honest

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
theorem validSoundnessCoefficient_one_le (r : ℕ) {edges : ℝ} (he : 0 ≤ edges) :
    1 ≤ validSoundnessCoefficient r edges := by
  have h := extractedSoundnessCoefficient_one_le r he
  unfold validSoundnessCoefficient
  linarith
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
    (validPauli : (ι → F) → PauliAnswer)
    (hvalid : ∀ x, projectPauli (validPauli x) = x)
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
    (hstate : ‖evec (isometricState VA VB ψ - registerState (ι → F) ξ)‖ ≤ t)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ t)
    (hX : ∑ x, snorm (registerState (ι → F) ξ) (aOp
      (isometricImage VA ((MA (QuestionType.pauli X, qX)).mats (.pauli (validPauli x))).val -
        (aOp (Honest.pauliXReadout (some x)) : Matrix ((ι → F) × H) _ ℂ))) ^ 2 ≤ t)
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      (isometricImage VB ((MB (QuestionType.pauli Z, qZ)).mats (.pauli (validPauli z))).val -
        (aOp (readout (some : (ι → F) → Option (ι → F)) (some z)) :
          Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ t) :
    1 - validSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
      iteratedRoot (6 * ℓ + 2) t ≤ quantumValue G := by
  have hE : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
  by_cases ht1 : t ≤ 1
  · have hnφ := registerState_norm (I := ι → F) ξ (norm_evec_eq_one_of_unit hξ)
    have hv (x : ι → F) : pauliProjection projectPauli
        (ParsedAnswer.pauli (A := A) (validPauli x)) = some x := by
      simp only [pauliProjection, hvalid]
    have hx := isometric_valid_outcome_alice_error_le VA hVA _ hnφ
      (MA (QuestionType.pauli X, qX)) (pauliProjection projectPauli)
      (fun x => .pauli (validPauli x)) hv (fun x => aOp (Honest.pauliXReadout x))
      Honest.pauliXReadout_isPVM.aOp (by rw [Honest.pauliXReadout_none, aOp_zero]) hX
    have hz := isometric_valid_outcome_bob_error_le VB hVB _ hnφ
      (MB (QuestionType.pauli Z, qZ)) (pauliProjection projectPauli)
      (fun x => .pauli (validPauli x)) hv (fun z => aOp (readout (some : (ι → F) → Option (ι → F)) z))
      (readout_isPVM some).aOp (by simp [readout, aOp_zero]) hZ
    have hs := Real.sqrt_nonneg t
    have htr : t ≤ Real.sqrt t := by
      simpa only [iteratedRoot] using self_le_iteratedRoot 1 ht ht1
    have hstate' : ‖evec (isometricState VA VB ψ - registerState (ι → F) ξ)‖ ^ 2 ≤
        6 * Real.sqrt t := by
      nlinarith [norm_nonneg (evec (isometricState VA VB ψ - registerState (ι → F) ξ)),
        mul_nonneg ht (sub_nonneg.mpr ht1)]
    have hout := quantumValue_ge_of_isometric_images E X Z P L hL projectPauli D DP
      G hμ hD ξ hξ ψ hψ VA VB hVA hVB MA MB hMA hMB qX qZ hqX hqZ
      (show 0 ≤ 6 * Real.sqrt t by positivity) hstate' (hfail.trans (by linarith))
      (by simpa only [stateSqNorm, stateNorm, norm_stateVec_eq_snorm] using
        hx.trans (show 2 * t + 4 * Real.sqrt t ≤ 6 * Real.sqrt t by linarith))
      (hz.trans (by linarith))
    have hr := iteratedRoot_scale_le (6 * ℓ + 1) (c := 6) (t := Real.sqrt t) (by norm_num)
    have he : iteratedRoot (6 * ℓ + 1) (Real.sqrt t) = iteratedRoot (6 * ℓ + 2) t := by
      simpa only [Nat.add_assoc, iteratedRoot] using
        (iteratedRoot_add (6 * ℓ + 1) 1 t).symm
    rw [he] at hr
    have hc := extractedSoundnessCoefficient_one_le ℓ hE
    unfold validSoundnessCoefficient
    nlinarith
  · have hc := validSoundnessCoefficient_one_le ℓ hE
    have hr : 1 ≤ iteratedRoot (6 * ℓ + 2) t := by
      simpa only [iteratedRoot_one] using iteratedRoot_mono (6 * ℓ + 2) (le_of_not_ge ht1)
    have hp : 1 ≤ validSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
        iteratedRoot (6 * ℓ + 2) t := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hr)]
    exact (by linarith : 1 - validSoundnessCoefficient ℓ
      (TypeGraph.edges E X Z ℓ).card * iteratedRoot (6 * ℓ + 2) t ≤ 0).trans
      (quantumValue_nonneg G)
end MIPRE.Introspection.TypedEstimates

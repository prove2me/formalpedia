-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_primitive_pauli
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:57:59.171801+00:00
-- url     : https://prove2.me/submissions/2b0613dc-4845-43b8-b7c1-33918ccb3de5

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/PrimitiveSoundness.lean (solution of MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_primitive_pauli);
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
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePowerBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveTerminalInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_TerminalOptionExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_PrimitiveSoundness
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_exists_intro_two_sided_iteration
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_hiding_register_rigidity_of_pauli
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_introAliceZError_le_of_bob
import Theorems.Thm_MIPRE_Introspection_TypedExtraction_exists_strategy_of_terminal_invariants
import Theorems.Thm_MIPRE_Introspection_adaptiveFailureBudget_le_power
import Theorems.Thm_MIPRE_Introspection_one_le_soundness_power_of_threshold_le
import Theorems.Thm_MIPRE_Introspection_primitiveSoundness_power_bounds
import Theorems.Thm_MIPRE_ancillaEmbed_isometry
import Theorems.Thm_MIPRE_dotProduct_star_self
import Theorems.Thm_MIPRE_swapVec_dotProduct

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem ExactlyOn.supportedOn {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    P.SupportedOn T := by
  induction P generalizing T with
  | zero => trivial
  | cons S L₁ next ih => exact ⟨hP.1, fun v => ih v (hP.2 v)⟩
end
end MIPRE.CL.CLFun

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

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {H : Type*} {K Ω : Type u}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype Ω] [DecidableEq Ω]
theorem introBobIterationState_unit (ξ : H × K → ℂ)
    (hξ : star ξ ⬝ᵥ ξ = 1) (a₀ : Ω) (n : ℕ) :
    star (introBobIterationState ξ a₀ n) ⬝ᵥ introBobIterationState ξ a₀ n = 1 := by
  rw [introBobIterationState, swapVec_dotProduct]
  exact introIterationState_unit (swapVec ξ) (by rwa [swapVec_dotProduct]) a₀ n
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {F ι A H K : Type u}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
theorem introTwoSidedState_unit (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1) (n : ℕ) :
    star (introTwoSidedState (F := F) (ι := ι) (A := A) ξ n) ⬝ᵥ
      introTwoSidedState ξ n = 1 :=
  introBobIterationState_unit _ (introIterationState_unit ξ hξ none n) none n
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
theorem adaptiveBudgetCoefficient_one_le (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ adaptiveBudgetCoefficient r edges := by
  have hm : 0 ≤ (512 * (r : ℝ) ^ 2 + 224) * edges := by positivity
  unfold adaptiveBudgetCoefficient
  linarith
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveSmallThreshold_le_one (r n : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    adaptiveSmallThreshold r edges n ≤ 1 := by
  have hC := adaptiveBudgetCoefficient_pos r hE
  calc
    _ ≤ adaptiveSmallThreshold r edges 0 :=
      adaptiveSmallThreshold_antitone r hE (Nat.zero_le n)
    _ ≤ 1 := by
      change 1 / adaptiveBudgetCoefficient r edges ≤ 1
      exact (div_le_iff₀ hC).mpr (by simpa only [one_mul] using
        adaptiveBudgetCoefficient_one_le r hE)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveFailureBudget_le_soundness_power (r n : ℕ)
    {edges z h initial t : ℝ} (hE : 0 ≤ edges) (ht0 : 0 ≤ t)
    (ht : t ≤ adaptiveSmallThreshold r edges n)
    (hi : initial ≤ t) (hz : z ≤ t) (hh : h ≤ t) :
    adaptiveFailureBudget r edges z h initial n ≤
      adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t := by
  exact (adaptiveFailureBudget_le_power r n hE ht0
    (ht.trans (adaptiveSmallThreshold_le_one r n hE)) hi hz hh).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (iteratedRoot_nonneg _ ht0))
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
/-- The full numerical dichotomy for any finite number of replacements:
either the original admissibility threshold holds and the actual recurrence
is bounded, or the very same power bound makes probability loss vacuous. -/
theorem adaptiveSoundness_power_cases (r n : ℕ) {edges z h initial t : ℝ}
    (hE : 0 ≤ edges) (ht0 : 0 ≤ t)
    (hi : initial ≤ t) (hz : z ≤ t) (hh : h ≤ t) :
    (t ≤ adaptiveSmallThreshold r edges n ∧
      adaptiveFailureBudget r edges z h initial n ≤
        adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t) ∨
      1 ≤ adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t := by
  by_cases ht : t ≤ adaptiveSmallThreshold r edges n
  · exact Or.inl ⟨ht, adaptiveFailureBudget_le_soundness_power r n hE ht0 ht hi hz hh⟩
  · exact Or.inr (one_le_soundness_power_of_threshold_le r n hE (le_of_not_ge ht))
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
theorem hidingPauliBudget_common (r : ℕ) (edges t : ℝ) :
    TypedEstimates.hidingPauliBudget r (edges * t) t t =
      TypedEstimates.hidingPauliBudget r edges 1 1 * t := by
  unfold TypedEstimates.hidingPauliBudget
  ring
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {F ι A H K : Type u} {PauliType PauliAnswer κ : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (hL : ∀ w, (L w).ExactlyOn univ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    (hMA : ∀ q, IsPVM (fun a => ((MA q).mats a).val))
    (hMB : ∀ q, IsPVM (fun a => ((MB q).mats a).val))
    (qX qZ : κ → ZMod 2)
    (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
    {t : ℝ} (ht : 0 ≤ t)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ t)
    (hX : ∑ x, stateSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val -
        (aOp (Honest.pauliXReadout x) : Matrix ((ι → F) × H) _ ℂ)) ≤ t)
    (hZ : introBobZError projectPauli Z qZ ξ MB ≤ t) :
    1 - primitiveSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
      iteratedRoot (6 * ℓ) t ≤ quantumValue G := by
  let edges : ℝ := (TypeGraph.edges E X Z ℓ).card
  have hE : 0 ≤ edges := Nat.cast_nonneg _
  let c := primitiveBudgetCoefficient ℓ edges
  let s := c * t
  have hc := primitiveBudgetCoefficient_bounds ℓ hE
  have hs : 0 ≤ s := mul_nonneg (by linarith [hc.1]) ht
  have hts : t ≤ s := le_mul_of_one_le_left ht hc.1
  have hpay := primitiveSoundness_power_bounds ℓ hE ht
  rcases adaptiveSoundness_power_cases ℓ (2 * ℓ) hE hs
    (le_refl s) (le_refl s) (le_refl s) with ⟨hsmall, hbound⟩ | hlarge
  · have hZA : introAliceZError projectPauli Z qZ ξ MA ≤ s := by
      apply (introAliceZError_le_of_bob E X Z P L projectPauli D DP
        ξ hξ MA MB qZ hqZ hfail hZ).trans
      calc
        _ = (4 * edges + 2) * t := by dsimp [edges]; ring
        _ ≤ s := mul_le_mul_of_nonneg_right hc.2.1 ht
    have hhide (w : Bool) (j : Fin ℓ) := hiding_register_rigidity_of_pauli
      E X Z P L projectPauli D DP ξ hξ MA MB hfail qX qZ hqX hqZ
      (hMA _) hX hZ w (hL w).supportedOn (hMA _) (fun j => hMA _) (fun j => hMB _) j
    have hhA (j : Fin ℓ) : hidingAliceError L false (hL false).supportedOn ξ MA j ≤ s := by
      apply (hhide false j).2.trans
      rw [hidingPauliBudget_common]
      calc
        _ = (4 * edges + 2 * hidingPauliBudget ℓ edges 1 1) * t := by dsimp [edges]; ring
        _ ≤ s := mul_le_mul_of_nonneg_right hc.2.2.2 ht
    have hhB (j : Fin ℓ) : hidingBobError L true (hL true).supportedOn ξ MB j ≤ s := by
      apply (hhide true j).1.trans
      rw [hidingPauliBudget_common]
      exact mul_le_mul_of_nonneg_right hc.2.2.1 ht
    obtain ⟨MAN, MBN, IA, IB, _, _, hf⟩ := exists_intro_two_sided_iteration
      E X Z P L projectPauli D DP ξ hξ MA MB hMA hMB qZ hqZ
      (fun w => (hL w).supportedOn) hs hs hs (hfail.trans hts) hZA
      (hZ.trans hts) hhA hhB hsmall hsmall hsmall
    obtain ⟨S, _, _, hS⟩ := TypedExtraction.exists_strategy_of_terminal_invariants
      E X Z P L hL projectPauli D DP G hμ hD (introTwoSidedState ξ ℓ)
      (introTwoSidedState_unit ξ hξ ℓ) MAN MBN IA IB hf
    have hbudget := (mul_le_mul_of_nonneg_left hbound hE).trans hpay.2
    have hvalue : S.value ≤ quantumValue G :=
      le_ciSup (TensorProductStrategy.bddAbove_range_value G) S
    exact (by linarith : 1 - primitiveSoundnessCoefficient ℓ edges *
      iteratedRoot (6 * ℓ) t ≤ S.value).trans hvalue
  · have htotal := hlarge.trans hpay.1
    exact (by linarith : 1 - primitiveSoundnessCoefficient ℓ edges *
      iteratedRoot (6 * ℓ) t ≤ 0).trans (quantumValue_nonneg G)
end MIPRE.Introspection.TypedEstimates

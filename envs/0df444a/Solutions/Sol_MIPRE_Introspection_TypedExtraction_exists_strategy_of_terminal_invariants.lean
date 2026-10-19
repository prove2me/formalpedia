-- Prove2me | solution 1 for MIPRE.Introspection.TypedExtraction.exists_strategy_of_terminal_invariants
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:35:46.680403+00:00
-- url     : https://prove2.me/submissions/cc367138-01fa-45f0-b9c9-4be59eb66960

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TerminalOptionExtraction.lean (solution of MIPRE.Introspection.TypedExtraction.exists_strategy_of_terminal_invariants);
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
import Theorems.Thm_MIPRE_Introspection_IntroPrefixInvariant_terminal_some
import Theorems.Thm_MIPRE_Introspection_TypedExtraction_condWin_cross_eq
import Theorems.Thm_MIPRE_Introspection_TypedExtraction_cross_failure_le
import Theorems.Thm_MIPRE_Introspection_introspectPair_map_some
import Theorems.Thm_MIPRE_Introspection_readoutAcceptance_le_completedValue
import Theorems.Thm_MIPRE_Introspection_registerOp_isPVM
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_SampledGame_dist_eq_card
import Theorems.Thm_MIPRE_TensorProductStrategy_value_eq_povmValue
import Theorems.Thm_MIPRE_bornProb_reindex
import Theorems.Thm_MIPRE_dotProduct_star_self
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

namespace MIPRE
section
open Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **The packaged strategy has the value of the original.** The two sides agree definitionally
once `TensorProductStrategy.value` is read as a `povmValue`: the packaged state is the reindexed
state and the packaged measurements are the reindexed POVMs. -/
theorem TensorProductStrategy.value_ofProjective (G : Game X Y A B) (ψ : dA × dB → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (PA : ProjectiveMeasurement X A (Matrix dA dA ℂ))
    (PB : ProjectiveMeasurement Y B (Matrix dB dB ℂ)) :
    (TensorProductStrategy.ofProjective G ψ hψ PA PB).value
      = povmValue G ψ (fun x => PA.toPOVM x) (fun y => PB.toPOVM y) := by
  rw [TensorProductStrategy.value_eq_povmValue]
  exact povmValue_reindex (Fintype.equivFin dA) (Fintype.equivFin dB) G ψ
    (fun x => PA.toPOVM x) (fun y => PB.toPOVM y)
end
end MIPRE

namespace MIPRE
section
open Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem TensorProductStrategy.value_ofPVM (G : Game X Y A B) (ψ : dA × dB → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (MA : X → POVM A dA) (MB : Y → POVM B dB)
    (hA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hB : ∀ y, IsPVM fun b => ((MB y).mats b).val) :
    (TensorProductStrategy.ofPVM G ψ hψ MA MB hA hB).value = povmValue G ψ MA MB := by
  rw [TensorProductStrategy.ofPVM, TensorProductStrategy.value_ofProjective]
  simp only [ProjectiveMeasurement.toPOVM_ofIsPVM]
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
variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
/-- In a CL sampler the EPR readout law is the sampler's actual question law. -/
theorem sampled_dist_eq_clDist {F ι : Type*} [Fintype F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (L R : (ι → F) → (ι → F)) (x y : ι → F) :
    SampledGame.dist L R x y = CL.clDist L R x y := by
  rw [SampledGame.dist_eq_card]
  unfold CL.clDist
  congr 2
  apply congrArg Finset.card
  ext s
  simp
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A H : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype H] [DecidableEq H] {ℓ : ℕ}
variable {P : CL.CLFun F ι ℓ}
  {N : POVM (Option ((ι → F) × A)) ((ι → F) × H)}
theorem terminalAuxPOVM_isPVM (hP : P.ExactlyOn univ)
    (I : IntroPrefixInvariant P ℓ N) (y : ι → F) :
    IsPVM (fun a => ((terminalAuxPOVM hP I y).mats a).val) := by
  unfold terminalAuxPOVM
  simpa only [registerPOVM_mats] using
    registerOp_isPVM (terminalResidualEquiv hP y)
      (isPVM_povm_map (I.residual y) (I.projective y) terminalAnswerMap)
end
end MIPRE.Introspection

namespace MIPRE.Introspection.TypedExtraction
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A] [DecidableEq A]
  [Fintype PauliAnswer] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  {ℓ : ℕ}
variable (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
/-- Terminal tensor-product pair effects identify the conditional value exactly.
No premise about the other parsed constructors is needed: the decider rejects them. -/
theorem condWin_cross_readout (ξ : H × K → ℂ)
    (QA : (ι → F) → A → Matrix H H ℂ) (QB : (ι → F) → A → Matrix K K ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    (hA : ∀ y a, ((MA (QuestionType.introspect false, 0)).mats (.pair y a)).val =
      conditionalReadout (L false).eval QA (y, a))
    (hB : ∀ y a, ((MB (QuestionType.introspect true, 0)).mats (.pair y a)).val =
      conditionalReadout (L true).eval QB (y, a)) :
    condWin (TypedEstimates.parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB
      (QuestionType.introspect false, 0) (QuestionType.introspect true, 0) =
        readoutAcceptance (L false).eval (L true).eval ξ QA QB D := by
  rw [condWin_cross_eq]
  simp_rw [hA, hB]
  rfl
end
end MIPRE.Introspection.TypedExtraction

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {A B H K : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
theorem completeOptionPOVM_isPVM (a₀ : A) (Q : POVM (Option A) H)
    (hQ : IsPVM (fun a => (Q.mats a).val)) :
    IsPVM (fun a => ((completeOptionPOVM a₀ Q).mats a).val) :=
  isPVM_povm_map Q hQ (fun a => a.getD a₀)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A H PauliAnswer : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype H] [DecidableEq H] [Fintype PauliAnswer] {ℓ : ℕ}
/-- The valid parsed effects of an actual terminal invariant have the
precise conditional readout form, regardless of malformed effects. -/
theorem IntroPrefixInvariant.terminal_parsed_pair
    {P : CL.CLFun F ι ℓ}
    {N : POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)}
    (I : IntroPrefixInvariant P ℓ (N.map TypedEstimates.introspectPair))
    (hP : P.ExactlyOn univ)
    (y : ι → F) (a : A) :
    (N.mats (.pair y a)).val = conditionalReadout P.eval
      (fun y a => ((terminalAuxPOVM hP I y).mats (some a)).val) (y, a) := by
  rw [← introspectPair_map_some]
  exact I.terminal_some hP y a
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedExtraction
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [DecidableEq A] [Nonempty A] [Fintype PauliAnswer]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
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
    (IA : IntroPrefixInvariant (L false) ℓ
      ((MA (QuestionType.introspect false, 0)).map TypedEstimates.introspectPair))
    (IB : IntroPrefixInvariant (L true) ℓ
      ((MB (QuestionType.introspect true, 0)).map TypedEstimates.introspectPair))
    {ε : ℝ} (hfail :
      1 - povmValue (TypedEstimates.parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F) ξ) MA MB ≤ ε) :
    ∃ S : TensorProductStrategy G,
      S.dA = Fintype.card H ∧ S.dB = Fintype.card K ∧
        1 - (TypeGraph.edges E X Z ℓ).card * ε ≤ S.value := by
  let a₀ : A := Classical.choice inferInstance
  let QA := terminalAuxPOVM (hL false) IA
  let QB := terminalAuxPOVM (hL true) IB
  let RA := fun y => completeOptionPOVM a₀ (QA y)
  let RB := fun y => completeOptionPOVM a₀ (QB y)
  have hRA (y : ι → F) : IsPVM (fun a => ((RA y).mats a).val) :=
    completeOptionPOVM_isPVM a₀ (QA y) (terminalAuxPOVM_isPVM (hL false) IA y)
  have hRB (y : ι → F) : IsPVM (fun a => ((RB y).mats a).val) :=
    completeOptionPOVM_isPVM a₀ (QB y) (terminalAuxPOVM_isPVM (hL true) IB y)
  let S := TensorProductStrategy.ofPVM G ξ hξ RA RB hRA hRB
  refine ⟨S, rfl, rfl, ?_⟩
  have hstate : star (registerState (ι → F) ξ) ⬝ᵥ registerState (ι → F) ξ = 1 := by
    rw [dotProduct_star_self, registerState_norm ξ (norm_evec_eq_one_of_unit hξ)]
    norm_num
  have hf := cross_failure_le E X Z P L projectPauli D DP
    (registerState (ι → F) ξ) hstate MA MB hfail
  have hc := condWin_cross_readout E X Z P L projectPauli D DP ξ
    (fun y a => ((QA y).mats (some a)).val)
    (fun y a => ((QB y).mats (some a)).val) MA MB
    (fun y a => IA.terminal_parsed_pair (hL false) y a)
    (fun y a => IB.terminal_parsed_pair (hL true) y a)
  rw [condFail, hc] at hf
  have hv := readoutAcceptance_le_completedValue G (L false).eval (L true).eval
    (fun x y => (hμ x y).trans (sampled_dist_eq_clDist _ _ x y).symm)
    ξ QA QB a₀ a₀
  rw [hD] at hv
  change 1 - (TypeGraph.edges E X Z ℓ).card * ε ≤
    (TensorProductStrategy.ofPVM G ξ hξ RA RB hRA hRB).value
  rw [TensorProductStrategy.value_ofPVM]
  exact (by linarith : 1 - (TypeGraph.edges E X Z ℓ).card * ε ≤
    readoutAcceptance (L false).eval (L true).eval ξ
      (fun y a => ((QA y).mats (some a)).val)
      (fun y a => ((QB y).mats (some a)).val) D).trans hv
end MIPRE.Introspection.TypedExtraction

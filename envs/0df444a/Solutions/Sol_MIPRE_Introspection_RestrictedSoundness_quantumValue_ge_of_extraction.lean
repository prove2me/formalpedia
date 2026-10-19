-- Prove2me | solution 1 for MIPRE.Introspection.RestrictedSoundness.quantumValue_ge_of_extraction
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T07:14:01.122981+00:00
-- url     : https://prove2.me/submissions/9eb7fb9c-e927-4df2-a638-a01cdc8f05ab

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/RestrictedSoundness.lean (solution of MIPRE.Introspection.RestrictedSoundness.quantumValue_ge_of_extraction);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
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
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Foundations_StrategyDilation
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_WeylBinary
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
import Definitions.Def_MIPRE_Foundations_Introspection_HonestMagicSquare
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliObservables
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliMeasurements
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCoreGame
import Definitions.Def_MIPRE_Foundations_Introspection_HonestReading
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsed
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsedHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCompleteAux
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliRegister
import Definitions.Def_MIPRE_Foundations_Introspection_HonestSampling
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliGame
import Definitions.Def_MIPRE_Background_Introspection_BinaryMeasurements
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRestriction
import Definitions.Def_MIPRE_Background_QLD_CLTransport
import Definitions.Def_MIPRE_Background_Introspection_PauliRestriction
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
import Definitions.Def_MIPRE_Background_Introspection_RestrictedSoundness
import Theorems.Thm_MIPRE_CL_CLFun_eval_reindex
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_quantumValue_ge_of_valid_isometric_images
import Theorems.Thm_MIPRE_SampledGame_dist_eq_card
import Theorems.Thm_MIPRE_TensorProductStrategy_value_eq_povmValue

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
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem norm_evec_eq_one_of_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) : ‖evec ψ‖ = 1 := by
  have h : ‖evec ψ‖ ^ 2 = 1 := by rw [norm_evec_sq, hψ, Complex.one_re]
  nlinarith [norm_nonneg (evec ψ), h]
end
end MIPRE

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
theorem compl_product_univ (S : Finset ι) :
    (S ×ˢ (Finset.univ : Finset κ))ᶜ = Sᶜ ×ˢ Finset.univ := by
  ext ⟨i, j⟩; simp
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
/-- `L^↓ = ↓ ∘ L ∘ ↓⁻¹`. -/
theorem eval_downsize (b : Module.Basis κ K F) (P : CLFun F ι ℓ) (x : ι → F) :
    (P.downsize b).eval (downsizeEquiv b x) = downsizeEquiv b (P.eval x) := by
  induction P generalizing x with
  | zero => simp
  | cons S L₁ next ih =>
    rw [downsize_cons, eval_cons, eval_cons, RegLinear.downsize_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, compl_product_univ,
      ← downsizeEquiv_proj, ih, map_add]
end
end MIPRE.CL.CLFun

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- Full Pauli questions have the literal zero content needed by the
introspection sampling and first-hiding edges. -/
theorem presentation_pauli_eval (hm : m ∣ Fintype.card F)
    (W : Bas) (x : Coord m → F) : (presentation hm (.pauli W)).eval x = 0 := by
  simp [presentation, seedMap, secondMap, finalMap]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t : ℕ} [NeZero m]
/-- Evaluation agrees with the actual field presentation under the binary
coordinate equivalence. -/
theorem binaryPresentation_eval (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (x : Coord m → F) :
    (binaryPresentation hm b T).eval (binaryVectorEquiv b x) =
      binaryVectorEquiv b ((presentation hm T).eval x) := by
  change (((presentation hm T).downsize b).reindex (binaryCoordEquiv m t)).eval
    (CL.reindexEquiv (binaryCoordEquiv m t) (CL.downsizeEquiv b x)) = _
  rw [CL.CLFun.eval_reindex, CL.CLFun.eval_downsize]
  rfl
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t : ℕ} [NeZero m]
theorem binaryPresentation_pauli_eval (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (W : Bas)
    (x : Fin ((3 * m + 3) * t) → ZMod 2) :
    (binaryPresentation hm b (.pauli W)).eval x = 0 := by
  obtain ⟨z, rfl⟩ := (binaryVectorEquiv (m := m) b).surjective x
  rw [binaryPresentation_eval, presentation_pauli_eval, map_zero]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {V A PA H K : Type*} [Fintype V] [Fintype A] [Fintype PA] [DecidableEq PA]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
theorem completePauliPOVM_mats (a₀ a : PA) (M : POVM (ParsedAnswer V A PA) H) :
    ((completePauliPOVM a₀ M).mats a).val =
      ∑ b ∈ univ.filter (fun b => completePauliAnswer a₀ b = a), (M.mats b).val :=
  POVM.map_mats _ _ _
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {V A PA H K : Type*} [Fintype V] [Fintype A] [Fintype PA] [DecidableEq PA]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- Only the selected completion answer changes its operator. -/
theorem completePauliPOVM_mats_of_ne (a₀ a : PA) (ha : a ≠ a₀)
    (M : POVM (ParsedAnswer V A PA) H) :
    ((completePauliPOVM a₀ M).mats a).val = (M.mats (.pauli a)).val := by
  rw [completePauliPOVM_mats]
  have hs : univ.filter (fun b : ParsedAnswer V A PA => completePauliAnswer a₀ b = a) =
      {.pauli a} := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    cases b <;> simp [completePauliAnswer, Ne.symm ha]
  rw [hs, sum_singleton]
end
end MIPRE.Introspection

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
theorem canonicalVector_pauli (W : Bas) :
    canonicalVector (F := F) (m := m) (.pauli W) = 0 := by
  funext i
  cases i with
  | point W i => cases W <;> rfl
  | scalar W => cases W <;> rfl
  | seed => rfl
  | direction i => rfl
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [Algebra (ZMod 2) F] [NeZero m] {t d : ℕ}
theorem pullbackStrategy_pauli_A (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (S : TensorProductStrategy (binaryGame (d := d) hm b)) (W : Bas) (a : Answer F m d) :
    (pullbackStrategy hm b S).PA.M (.pauli W) a = S.PA.M (.pauli W, 0) a := by
  simp only [pullbackStrategy, ProjectiveMeasurement.reindex_M, Equiv.refl_apply,
    encodeQuestion, Question.ty, canonicalVector_pauli, map_zero]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [Algebra (ZMod 2) F] [NeZero m] {t d : ℕ}
theorem pullbackStrategy_pauli_B (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (S : TensorProductStrategy (binaryGame (d := d) hm b)) (W : Bas) (a : Answer F m d) :
    (pullbackStrategy hm b S).PB.M (.pauli W) a = S.PB.M (.pauli W, 0) a := by
  simp only [pullbackStrategy, ProjectiveMeasurement.reindex_M, Equiv.refl_apply,
    encodeQuestion, Question.ty, canonicalVector_pauli, map_zero]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.Introspection.PauliRestriction
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
  (S : TensorProductStrategy (fullGame hm b L project D))
theorem strategy_pauli_A (a₀ b₀ : QLD.Answer F m d) (W : QLD.Bas) (a : QLD.Answer F m d) :
    (strategy hm b L project D S a₀ b₀).PA.M (.pauli W) a =
      ((completePauliPOVM a₀ (S.PA.toPOVM (QuestionType.pauli (.pauli W),0))).mats a).val := by
  exact QLD.PauliCL.pullbackStrategy_pauli_A hm b
    (binaryStrategy hm b L project D S a₀ b₀) W a
end
end MIPRE.Introspection.PauliRestriction

namespace MIPRE.Introspection.PauliRestriction
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
  (S : TensorProductStrategy (fullGame hm b L project D))
theorem strategy_pauli_B (a₀ b₀ : QLD.Answer F m d) (W : QLD.Bas) (a : QLD.Answer F m d) :
    (strategy hm b L project D S a₀ b₀).PB.M (.pauli W) a =
      ((completePauliPOVM b₀ (S.PB.toPOVM (QuestionType.pauli (.pauli W),0))).mats a).val := by
  exact QLD.PauliCL.pullbackStrategy_pauli_B hm b
    (binaryStrategy hm b L project D S a₀ b₀) W a
end
end MIPRE.Introspection.PauliRestriction

namespace MIPRE.Introspection.PauliRestriction
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
  (S : TensorProductStrategy (fullGame hm b L project D))
/-- Choosing a scalar completion answer leaves every genuine Pauli answer
operator exactly unchanged, even when malformed outer answers have mass. -/
theorem strategy_pauliAns_A (W : QLD.Bas) (a : (Fin m → Bool) → F) :
    (strategy hm b L project D S (.val 0) (.val 0)).PA.M (.pauli W) (.pauliAns a) =
      S.PA.M (QuestionType.pauli (.pauli W),0) (.pauli (.pauliAns a)) := by
  rw [strategy_pauli_A, completePauliPOVM_mats_of_ne _ _ (by intro h; cases h)]
  rfl
end
end MIPRE.Introspection.PauliRestriction

namespace MIPRE.Introspection.PauliRestriction
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
  (S : TensorProductStrategy (fullGame hm b L project D))
theorem strategy_pauliAns_B (W : QLD.Bas) (a : (Fin m → Bool) → F) :
    (strategy hm b L project D S (.val 0) (.val 0)).PB.M (.pauli W) (.pauliAns a) =
      S.PB.M (QuestionType.pauli (.pauli W),0) (.pauli (.pauliAns a)) := by
  rw [strategy_pauli_B, completePauliPOVM_mats_of_ne _ _ (by intro h; cases h)]
  rfl
end
end MIPRE.Introspection.PauliRestriction

namespace MIPRE.Introspection.RestrictedSoundness
noncomputable section
open Matrix Finset Classical BinaryComplete
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t d ℓ : ℕ} [NeZero m]
  {A H K : Type} [Fintype A] [Nonempty A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
theorem project_validAnswer (b : Module.Basis (Fin t) (ZMod 2) F) (x : Seed m t) :
    BinaryComplete.project b (validAnswer (d := d) b x) = x :=
  (Weyl.binEquiv b).apply_symm_apply x
end
end MIPRE.Introspection.RestrictedSoundness

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.RestrictedSoundness
open Matrix Finset Classical BinaryComplete
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t d ℓ : ℕ} [NeZero m]
  {A H K : Type} [Fintype A] [Nonempty A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (S : TensorProductStrategy
    (PauliRestriction.fullGame hm b L (BinaryComplete.project (d := d) b) D))
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution
    (hL : ∀ w, (L w).ExactlyOn univ)
    (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (VA : Matrix (Seed m t × H) (Fin S.dA) ℂ)
    (VB : Matrix (Seed m t × K) (Fin S.dB) ℂ)
    (hVA : VAᴴ * VA = 1) (hVB : VBᴴ * VB = 1)
    {ε δ : ℝ} (hδ : 0 ≤ δ) (hfail : 1 - S.value ≤ ε)
    (hstate : ‖evec (isometricState VA VB (restriction hm b L D S).ψ -
      registerState (Seed m t) ξ)‖ ≤ δ)
    (hX : ∑ x : Seed m t, snorm (registerState (Seed m t) ξ) (aOp
      (isometricImage VA ((restriction hm b L D S).PA.M (.pauli .X) (validAnswer b x)) -
        (aOp (Honest.pauliXReadout (some x)) : Matrix (Seed m t × H) _ ℂ))) ^ 2 ≤ δ)
    (hZ : ∑ z : Seed m t, snorm (registerState (Seed m t) ξ) (bOp
      (isometricImage VB ((restriction hm b L D S).PB.M (.pauli .Z) (validAnswer b z)) -
        (aOp (readout (some : Seed m t → Option (Seed m t)) (some z)) :
          Matrix (Seed m t × K) _ ℂ))) ^ 2 ≤ δ) :
    1 - validSoundnessCoefficient ℓ
      (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card *
      iteratedRoot (6 * ℓ + 2) (max ε δ) ≤ quantumValue (Honest.sourceGame L D) := by
  apply TypedEstimates.quantumValue_ge_of_valid_isometric_images
    QLD.adj (.pauli .X) (.pauli .Z) (QLD.PauliCL.binaryPresentation hm b) L hL
    (BinaryComplete.project b) (validAnswer b) (project_validAnswer b)
    D (PauliRestriction.pauliCheck hm b) (Honest.sourceGame L D)
    (by
      intro x y
      change SampledGame.dist _ _ x y = _
      rw [SampledGame.dist_eq_card]
      unfold CL.clDist
      congr 2
      apply congrArg Finset.card
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]) rfl ξ hξ S.ψ
    (norm_evec_eq_one_of_unit S.ψ_unit)
    VA VB hVA hVB S.PA.toPOVM S.PB.toPOVM
    (fun q => ⟨S.PA.selfAdjoint q, S.PA.projective q, S.PA.normalized q⟩)
    (fun q => ⟨S.PB.selfAdjoint q, S.PB.projective q, S.PB.normalized q⟩)
    0 0 (QLD.PauliCL.binaryPresentation_pauli_eval hm b .X)
    (QLD.PauliCL.binaryPresentation_pauli_eval hm b .Z)
    (hδ.trans (le_max_right ε δ)) (hstate.trans (le_max_right ε δ))
  · change 1 - povmValue _ S.ψ S.PA.toPOVM S.PB.toPOVM ≤ max ε δ
    rw [← TensorProductStrategy.value_eq_povmValue]
    exact hfail.trans (le_max_left ε δ)
  · have hh := hX.trans (le_max_right ε δ)
    simpa only [restriction, validAnswer, PauliRestriction.strategy_pauliAns_A,
      ProjectiveMeasurement.toPOVM] using hh
  · have hh := hZ.trans (le_max_right ε δ)
    simpa only [restriction, validAnswer, PauliRestriction.strategy_pauliAns_B,
      ProjectiveMeasurement.toPOVM] using hh
end MIPRE.Introspection.RestrictedSoundness

-- Prove2me | solution 1 for MIPRE.Introspection.exists_adaptive_prefix_dilation
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:40:07.949002+00:00
-- url     : https://prove2.me/submissions/0ea0bc4b-4586-4001-84fd-be82574346df

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptivePrefixReplacement.lean (solution of MIPRE.Introspection.exists_adaptive_prefix_dilation);
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
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacementRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDilationTransport
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixReplacement
import Theorems.Thm_MIPRE_Introspection_dilated_pvm_distance
import Theorems.Thm_MIPRE_Introspection_exists_register_mixing_sqrt
import Theorems.Thm_MIPRE_Introspection_norm_evec_comp_equiv
import Theorems.Thm_MIPRE_Introspection_prefixProjector_weight
import Theorems.Thm_MIPRE_Introspection_readout_isPVM
import Theorems.Thm_MIPRE_Introspection_registerEPR_equiv
import Theorems.Thm_MIPRE_Introspection_registerOp_isPVM
import Theorems.Thm_MIPRE_Introspection_registerOp_kronecker
import Theorems.Thm_MIPRE_Introspection_registerOp_mulVec
import Theorems.Thm_MIPRE_Introspection_stateSqNorm_registerExtend
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_Weyl_isPVM_synOf
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wZ
import Theorems.Thm_MIPRE_exists_projective_dilation
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_mulVec_kron_expVec
import Theorems.Thm_MIPRE_norm_evec_expVec
import Theorems.Thm_MIPRE_sum_kronecker_left
import Theorems.Thm_MIPRE_sum_weighted_mul_le_sqrt

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateSqNorm_nonneg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : 0 ≤ stateSqNorm ψ M :=
  sq_nonneg _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
/-- **Moving an average inside a square root.** Cauchy--Schwarz against the constant one. -/
theorem sum_weighted_sqrt_le {ι : Type*} [Fintype ι] (w f : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hf : ∀ i, 0 ≤ f i) :
    ∑ i, w i * Real.sqrt (f i) ≤ Real.sqrt (∑ i, w i * f i) := by
  have h := sum_weighted_mul_le_sqrt w (fun i => Real.sqrt (f i)) (fun _ => (1 : ℝ)) hw0
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => show
      w i * (Real.sqrt (f i) * 1) = w i * Real.sqrt (f i) from by rw [mul_one],
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => show
      w i * Real.sqrt (f i) ^ 2 = w i * f i from by rw [Real.sq_sqrt (hf i)],
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => show w i * (1 : ℝ) ^ 2 = w i from by ring,
    hw1, Real.sqrt_one, mul_one] at h
  exact h
end
end MIPRE

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
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
theorem readoutWeight_nonneg (f : I → X) (x : X) : 0 ≤ readoutWeight f x :=
  SampledGame.dist_nonneg f (fun _ => ()) x ()
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
theorem sum_readoutWeight [Nonempty I] (f : I → X) : ∑ x, readoutWeight f x = 1 := by
  simpa only [readoutWeight, Fintype.sum_unique] using SampledGame.sum_dist f (fun _ => ())
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem prefixWeight_nonneg (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    0 ≤ prefixWeight P k y := readoutWeight_nonneg _ _
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem sum_prefixWeight (P : CL.CLFun F ι ℓ) (k : ℕ) :
    ∑ y, prefixWeight P k y = 1 := sum_readoutWeight _
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
/-- Consistency on the ambient state is exactly consistency on the local EPR factor. -/
theorem ambientMarginalError_eq (U V : Finset ι) (hUV : U ⊆ V)
    (L : CL.RegLinear F U) (ξ : H × K → ℂ)
    (M : (Fin (Fintype.card U) → F) × A → Matrix ((V → F) × H) ((V → F) × H) ℂ) :
    ambientMarginalError U V hUV L ξ M =
      registerMarginalError (coordinateSplit U V hUV) (coordinateLinear L) ξ M := by
  unfold ambientMarginalError registerMarginalError ambientReadout ambientOperator
  simp_rw [← registerExtend_sum, ← registerExtend_sub, stateSqNorm_registerExtend]
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
  [Fintype A] [DecidableEq A]
/-- **Ambient Pauli mixing.** The finite-set register inclusions, the CL linear maps,
and the one global EPR state are supplied directly. The output measurements have precisely
the local residual register as support. All answer values, including those outside the
linear map's range, occur in the sums; the error is at most `56 sqrt ε`. -/
theorem exists_ambient_pauli_mixing {X : Type*} [Fintype X]
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (U V : X → Finset ι) (hUV : ∀ x, U x ⊆ V x)
    (L : (x : X) → CL.RegLinear F (U x))
    (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (M : (x : X) → POVM ((Fin (Fintype.card (U x)) → F) × A) ((V x → F) × H))
    (hM : ∀ x, IsPVM (fun p => ((M x).mats p).val))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : ∑ x, D x * ambientMarginalError (U x) (V x) (hUV x) (L x) ξ
      (fun p => ((M x).mats p).val) ≤ ε)
    (hZ : ∑ x, D x * ambientCommutatorError (U x) (V x) (hUV x) ξ
      (fun p => ((M x).mats p).val) wZ LinearMap.id ≤ ε)
    (hX : ∑ x, D x * ambientCommutatorError (U x) (V x) (hUV x) ξ
      (fun p => ((M x).mats p).val) wX (CL.lperp (coordinateLinear (L x))) ≤ ε) :
    ∃ Q : (x : X) → (Fin (Fintype.card (U x)) → F) → POVM A ((↥(V x \ U x) → F) × H),
      (∑ x, D x * ∑ p : (Fin (Fintype.card (U x)) → F) × A,
        stateSqNorm (registerState (ι → F) ξ)
          (ambientOperator (V x) ((M x).mats p).val -
            ambientOperator (V x) (registerOp
              (registerParty (coordinateSplit (U x) (V x) (hUV x)) H)
              (synOf wZ (coordinateLinear (L x)) p.1 ⊗ₖ ((Q x p.1).mats p.2).val)))) ≤
        56 * Real.sqrt ε := by
  simp_rw [ambientMarginalError_eq] at hmarg
  simp_rw [ambientCommutatorError_eq] at hZ hX
  obtain ⟨Q, hQ⟩ := exists_register_mixing_sqrt D hD0 hD1
    (fun x => coordinateSplit (U x) (V x) (hUV x))
    (fun x => coordinateLinear (L x)) ξ hξ M hM hε0 hε1 hmarg hZ hX
  refine ⟨Q, ?_⟩
  unfold ambientOperator
  simpa only [← registerExtend_sub, stateSqNorm_registerExtend] using hQ
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
theorem prefixStageMarginalError_eq (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix ((stageRemaining P k y → F) × H) _ ℂ) :
    prefixStageMarginalError P hP k ξ M = ∑ y, prefixWeight P k y *
      ambientMarginalError (P.factorOfPrefix k y) (stageRemaining P k y)
        (stageFactor_subset_remaining P hP k y) (CLChecks.stageLinear P k y) ξ (M y) := by
  simp only [prefixStageMarginalError, prefixResidual_distance P hP,
    ambientMarginalError_eq, registerMarginalError, stageSplit, Finset.mul_sum]
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
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
/-- **One adaptive extraction step.** The three errors are measured on the
original EPR-plus-auxiliary state. The theorem constructs the next residual
POVMs on the actual next unvisited coordinates; no prefix distribution,
support identification, or product-form conclusion is an input. -/
theorem exists_adaptive_prefix_mixing (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : prefixStageMarginalError P hP k ξ (fun y p => ((M y).mats p).val) ≤ ε)
    (hZ : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ ε)
    (hX : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) ≤ ε) :
    ∃ Q : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      POVM A ((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H),
      (∑ y, ∑ p : (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A,
        stateSqNorm (registerState (ι → F) ξ)
          (prefixResidualOp P k y ((M y).mats p).val -
            prefixResidualOp P k y (registerOp (registerParty (stageSplit P hP k y) H)
              (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y)) p.1 ⊗ₖ
                ((Q y p.1).mats p.2).val)))) ≤ 56 * Real.sqrt ε := by
  rw [prefixStageMarginalError_eq] at hmarg
  rw [prefixStageCommutatorError_eq] at hZ hX
  obtain ⟨Q, hQ⟩ := exists_ambient_pauli_mixing (prefixWeight P k)
    (prefixWeight_nonneg P k) (sum_prefixWeight P k)
    (P.factorOfPrefix k) (stageRemaining P k) (stageFactor_subset_remaining P hP k)
    (CLChecks.stageLinear P k) ξ hξ M hM hε0 hε1 hmarg hZ hX
  refine ⟨Q, ?_⟩
  simpa only [prefixResidual_distance P hP, ← Finset.mul_sum, ambientOperator,
    ← registerExtend_sub, stateSqNorm_registerExtend, stageSplit] using hQ
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {I H K Y A J : Type*}
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A] [Fintype J]
/-- Compression to a fixed ancilla slice is literally the corresponding
matrix subblock. -/
theorem ancilla_compress_apply (a₀ : A) (M : Matrix (H × A) (H × A) ℂ) (i j : H) :
    ((ancillaEmbed H a₀)ᴴ * (M * ancillaEmbed H a₀)) i j = M (i, a₀) (j, a₀) := by
  simp [Matrix.mul_apply, ancillaEmbed, Matrix.conjTranspose_apply]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {I H K Y A J : Type*}
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A] [Fintype J]
/-- Conditional projective residual measurements keep the joint measurement
projective while leaving every prefix projector untouched. -/
theorem conditionalDilationOp_isPVM (Z : Y → Matrix I I ℂ) (hZ : IsPVM Z)
    (P : Y → A → Matrix (H × A) (H × A) ℂ) (hP : ∀ y, IsPVM (P y)) :
    IsPVM (conditionalDilationOp Z P) := by
  apply registerOp_isPVM
  refine ⟨fun p => ?_, fun p => ?_, ?_⟩
  · rw [Matrix.conjTranspose_kronecker, hZ.isSelfAdjoint, (hP _).isSelfAdjoint]
  · rw [← Matrix.mul_kronecker_mul, hZ.idem, (hP _).idem]
  · rw [Fintype.sum_prod_type]
    simp_rw [← kronecker_sum_right, (hP _).sum_eq_one]
    rw [← sum_kronecker_left, hZ.sum_eq_one, Matrix.one_kronecker_one]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {I H K Y A J : Type*}
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A] [Fintype J]
/-- The full conditional dilation compresses to the desired prefix times
residual POVM, using the same embedding for every prefix and outcome. -/
theorem conditionalDilationOp_compress (a₀ : A) (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix (H × A) (H × A) ℂ)
    (R : Y → A → Matrix H H ℂ)
    (hk : ∀ y a, (ancillaEmbed H a₀)ᴴ * (P y a * ancillaEmbed H a₀) = R y a)
    (p : Y × A) :
    (ancillaEmbed (I × H) a₀)ᴴ *
      (conditionalDilationOp Z P p * ancillaEmbed (I × H) a₀) = Z p.1 ⊗ₖ R p.1 p.2 := by
  ext i j
  rw [ancilla_compress_apply]
  change Z p.1 i.1 j.1 * P p.1 p.2 (i.2, a₀) (j.2, a₀) =
    Z p.1 i.1 j.1 * R p.1 p.2 i.2 j.2
  rw [← ancilla_compress_apply a₀ (P p.1 p.2) i.2 j.2, hk]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {V I R H K Y A : Type*}
  [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A]
/-- Ancilla compression commutes with a relabelling of the old register. -/
theorem ancilla_compress_registerOp (e : V ≃ I) (a₀ : A)
    (M : Matrix (I × A) (I × A) ℂ) :
    (ancillaEmbed V a₀)ᴴ *
      (registerOp (e.prodCongr (Equiv.refl A)) M * ancillaEmbed V a₀) =
      registerOp e ((ancillaEmbed I a₀)ᴴ * (M * ancillaEmbed I a₀)) := by
  ext i j
  simp only [ancilla_compress_apply, registerOp_apply]
  rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {V I R H K Y A : Type*}
  [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A]
theorem transportedConditionalDilation_isPVM (e : V ≃ I × R)
    (Z : Y → Matrix I I ℂ) (hZ : IsPVM Z)
    (P : Y → A → Matrix ((R × H) × A) ((R × H) × A) ℂ)
    (hP : ∀ y, IsPVM (P y)) : IsPVM (transportedConditionalDilation e Z P) :=
  registerOp_isPVM _ (conditionalDilationOp_isPVM Z hZ P hP)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {V I R H K Y A : Type*}
  [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A]
theorem transportedConditionalDilation_compress (e : V ≃ I × R) (a₀ : A)
    (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix ((R × H) × A) ((R × H) × A) ℂ)
    (Q : Y → POVM A (R × H))
    (hk : ∀ y a, (ancillaEmbed (R × H) a₀)ᴴ * (P y a * ancillaEmbed (R × H) a₀) =
      ((Q y).mats a).val) (p : Y × A) :
    (ancillaEmbed (V × H) a₀)ᴴ *
      (transportedConditionalDilation e Z P p * ancillaEmbed (V × H) a₀) =
      registerOp (registerParty e H) (Z p.1 ⊗ₖ ((Q p.1).mats p.2).val) := by
  rw [transportedConditionalDilation, ancilla_compress_registerOp,
    conditionalDilationOp_compress a₀ Z P (fun y a => ((Q y).mats a).val) hk]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem _root_.solution (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1) (a₀ : A)
    (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : prefixStageMarginalError P hP k ξ (fun y p => ((M y).mats p).val) ≤ ε)
    (hZ : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ ε)
    (hX : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) ≤ ε) :
    ∃ D : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      A → Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A)
        (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) ℂ,
      (∀ y z, IsPVM (D y z)) ∧
      (∑ y, prefixWeight P k y * ∑ p,
        stateSqNorm (extVecA (registerState (stageRemaining P k y → F) ξ) a₀)
          (aOp ((M y).mats p).val - transportedConditionalDilation (stageSplit P hP k y)
            (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y) p)) ≤
        2*Real.sqrt (56*Real.sqrt ε) := by
  obtain ⟨Q, hQ⟩ := exists_adaptive_prefix_mixing P hP k ξ hξ M hM hε0 hε1 hmarg hZ hX
  have hlocal y : ∃ D : (Fin (Fintype.card (P.factorOfPrefix k y)) → F) → A →
      Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A)
        (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) ℂ,
      (∀ z, IsPVM (D z)) ∧
      (∀ z a, (ancillaEmbed ((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) a₀)ᴴ *
        (D z a * ancillaEmbed ((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) a₀) =
          ((Q y z).mats a).val) := by
    obtain ⟨D, hsa, hid, hsum, hk⟩ := exists_projective_dilation a₀
      (E := fun z a => ((Q y z).mats a).val)
      (fun z a => (Q y z).posSemidef a) (fun z => (Q y z).sum_val)
    refine ⟨D, fun z => ⟨?_, hid z, hsum z⟩, hk⟩
    intro a
    rw [← Matrix.star_eq_conjTranspose]
    exact hsa z a
  choose D hD hk using hlocal
  refine ⟨D, hD, ?_⟩
  let err y := ∑ p, stateSqNorm (registerState (stageRemaining P k y → F) ξ)
    (((M y).mats p).val - registerOp (registerParty (stageSplit P hP k y) H)
      (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y)) p.1 ⊗ₖ
        ((Q y p.1).mats p.2).val))
  have herr y : 0 ≤ err y := Finset.sum_nonneg fun _ _ => stateSqNorm_nonneg _ _
  have havg : ∑ y, prefixWeight P k y * err y ≤ 56*Real.sqrt ε := by
    simpa only [prefixResidual_distance P hP, Finset.mul_sum, err] using hQ
  have hpoint y := dilated_pvm_distance (registerState (stageRemaining P k y → F) ξ)
    (registerState_norm ξ hξ) a₀ (fun p => ((M y).mats p).val)
    (fun p => registerOp (registerParty (stageSplit P hP k y) H)
      (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y)) p.1 ⊗ₖ
        ((Q y p.1).mats p.2).val))
    (transportedConditionalDilation (stageSplit P hP k y)
      (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y))
    (hM y) (transportedConditionalDilation_isPVM _ _ (isPVM_synOf isWeylFamily_wZ _) _ (hD y))
    (transportedConditionalDilation_compress _ a₀ _ _ (Q y) (hk y)) (δ := err y) le_rfl
  calc
    _ ≤ ∑ y, prefixWeight P k y * (2*Real.sqrt (err y)) :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpoint y) (prefixWeight_nonneg P k y)
    _ = 2*∑ y, prefixWeight P k y * Real.sqrt (err y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ 2*Real.sqrt (56*Real.sqrt ε) := mul_le_mul_of_nonneg_left
      ((sum_weighted_sqrt_le (prefixWeight P k) err (prefixWeight_nonneg P k)
        (sum_prefixWeight P k) herr).trans (Real.sqrt_le_sqrt havg)) (by norm_num)
end MIPRE.Introspection

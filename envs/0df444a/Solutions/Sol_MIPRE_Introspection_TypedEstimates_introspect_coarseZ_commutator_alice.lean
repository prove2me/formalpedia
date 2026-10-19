-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.introspect_coarseZ_commutator_alice
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:54:01.04168+00:00
-- url     : https://prove2.me/submissions/0eedd93e-d143-439d-a6db-a44222d4f176

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ProductStageZTests.lean (solution of MIPRE.Introspection.TypedEstimates.introspect_coarseZ_commutator_alice);
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
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_PauliAuxEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingRegister
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInduction
import Definitions.Def_MIPRE_Foundations_Introspection_HidingBaseOperators
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageZTests
import Theorems.Thm_MIPRE_Introspection_TypeGraph_symmetric
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_aux_agreement_estimate
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_constant_edge_agreement_estimate
import Theorems.Thm_MIPRE_Introspection_coarse_joint_commutator_bound
import Theorems.Thm_MIPRE_Introspection_readout_isPVM
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_POVM_map_map
import Theorems.Thm_MIPRE_POVM_sum_mats_map_prod
import Theorems.Thm_MIPRE_POVM_sum_mats_map_prod_prime
import Theorems.Thm_MIPRE_Weyl_stateVec_epr
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_dotProduct_star_self
import Theorems.Thm_MIPRE_mulVec_kron_kron_expVec
import Theorems.Thm_MIPRE_norm_evec_expVec
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_eq
import Theorems.Thm_MIPRE_sum_bornProb_le_fibSum
import Theorems.Thm_MIPRE_sum_xSqNorm_le_of_two_step

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
omit [Fintype N] in
theorem evec_sub (v w : N → ℂ) : evec (v - w) = evec v - evec w := rfl
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
variable (v : N → ℂ)
theorem snorm_nonneg (M : Matrix N N ℂ) : 0 ≤ snorm v M := norm_nonneg _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_add_le (M M' : Matrix N N ℂ) : snorm v (M + M') ≤ snorm v M + snorm v M' := by
  rw [snorm, snorm, snorm, Matrix.add_mulVec, evec_add]
  exact norm_add_le _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_sub_comm (M M' : Matrix N N ℂ) : snorm v (M - M') = snorm v (M' - M) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, evec_sub, evec_sub, norm_sub_rev]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_add (X Y : Matrix HB HB ℂ) :
    bOp (X + Y) = (bOp X : Matrix (HA × HB) _ ℂ) + bOp Y := Matrix.kronecker_add _ _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_smul (c : ℂ) (X : Matrix HB HB ℂ) :
    bOp (c • X) = c • (bOp X : Matrix (HA × HB) _ ℂ) := Matrix.kronecker_smul _ _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_sub (X Y : Matrix HB HB ℂ) :
    bOp (X - Y) = (bOp X : Matrix (HA × HB) _ ℂ) - bOp Y := by
  have h : X - Y = X + (-1 : ℂ) • Y := by module
  rw [h, bOp_add, bOp_smul]
  module
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
theorem xSqNorm_eq_sq (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = xNorm ψ A B ^ 2 := rfl
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
/-- The deviation is the state-norm of the single operator `A ⊗ Id - Id ⊗ B` on the product
space, which is what the operator-norm calculus of `MIPRE/Foundations/OpBound.lean` consumes. -/
theorem xNorm_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xNorm ψ A B = snorm ψ ((aOp A : Matrix (dA × dB) _ ℂ) - bOp B) := by
  rw [xNorm, snorm, Matrix.sub_mulVec, evec_sub]
  rfl
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
/-- The squared cross-party deviation as a `snorm` on the joint space, which is the form the
chains of the appendix are run in. -/
theorem xSqNorm_eq_snorm_sq (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = snorm ψ ((aOp A : Matrix (dA × dB) (dA × dB) ℂ) - bOp B) ^ 2 := by
  rw [xSqNorm_eq_sq, xNorm_eq_snorm]
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
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- The triangle inequality for a family of deviations, at the usual cost of a factor two. -/
theorem sum_snorm_sq_triangle' {ι : Type*} [Fintype ι] (v : N → ℂ)
    (P Q R : ι → Matrix N N ℂ) :
    ∑ i, snorm v (P i - R i) ^ 2
      ≤ 2 * ∑ i, snorm v (P i - Q i) ^ 2 + 2 * ∑ i, snorm v (Q i - R i) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsplit : P i - R i = (P i - Q i) + (Q i - R i) := by abel
  have htri : snorm v (P i - R i) ≤ snorm v (P i - Q i) + snorm v (Q i - R i) := by
    rw [hsplit]; exact snorm_add_le v _ _
  nlinarith [snorm_nonneg v (P i - Q i), snorm_nonneg v (Q i - R i),
    snorm_nonneg v (P i - R i), sq_nonneg (snorm v (P i - Q i) - snorm v (Q i - R i))]
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
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
theorem isPVM_fibSum {G : α → Matrix N N ℂ} (h : IsPVM G) (e : α → β) : IsPVM (fibSum G e) :=
  h.coarse e
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
/-- **Coarse-graining two projective families the same way costs nothing**, in the `fibSum` form
that the pasting lemma needs. -/
theorem sum_xSqNorm_fibSum_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {X : α → Matrix dA dA ℂ}
    {X' : α → Matrix dB dB ℂ} (hX : IsPVM X) (hX' : IsPVM X') (e : α → β) :
    ∑ b, xSqNorm ψ (fibSum X e b) (fibSum X' e b) ≤ ∑ a, xSqNorm ψ (X a) (X' a) := by
  have e1 := one_sub_sum_bornProb_eq hψ (isPVM_fibSum hX e) (isPVM_fibSum hX' e)
  have e2 := one_sub_sum_bornProb_eq hψ hX hX'
  have e3 := sum_bornProb_le_fibSum ψ hX hX' e
  linarith
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl
open scoped Kronecker
variable {V W H K : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- Exact consistency survives adjoining any bipartite ancillary state. -/
theorem mirror_expVec (ψ : V × W → ℂ) (ξ : H × K → ℂ)
    (P : Matrix V V ℂ) (Q : Matrix W W ℂ) (h : stateVec ψ P = stateVecB ψ Q) :
    stateVec (expVec ψ ξ) (aOp P : Matrix (V × H) _ ℂ) =
      stateVecB (expVec ψ ξ) (aOp Q : Matrix (W × K) _ ℂ) := by
  have hbase := congrArg WithLp.ofLp h
  change (P ⊗ₖ (1 : Matrix W W ℂ)) *ᵥ ψ = ((1 : Matrix V V ℂ) ⊗ₖ Q) *ᵥ ψ at hbase
  unfold stateVec stateVecB aOp
  congr 1
  rw [show (1 : Matrix (W × K) (W × K) ℂ) =
      (1 : Matrix W W ℂ) ⊗ₖ (1 : Matrix K K ℂ) from Matrix.one_kronecker_one.symm,
    show (1 : Matrix (V × H) (V × H) ℂ) =
      (1 : Matrix V V ℂ) ⊗ₖ (1 : Matrix H H ℂ) from Matrix.one_kronecker_one.symm,
    mulVec_kron_kron_expVec, mulVec_kron_kron_expVec, hbase]
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
/-- The finite-basis EPR definition agrees literally with the Weyl-register definition. -/
theorem registerEPR_eq_weyl {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    registerEPR (ι → F) = Weyl.epr (F := F) (n := ι) := rfl
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

namespace MIPRE.Introspection.TypedPredicate
noncomputable section
open Classical
variable {PauliType PauliAnswer F ι A : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
/-- Accepted answers have the correct constructors on both sides. -/
theorem check_formats {t u : QuestionType PauliType ℓ}
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : check L X Z projectPauli D DP t u a b = true) : fits t a = true ∧ fits u b = true := by
  simp only [check, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2⟩
end
end MIPRE.Introspection.TypedPredicate

namespace MIPRE.Introspection.TypedPredicate
noncomputable section
open Classical
variable {PauliType PauliAnswer F ι A : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
/-- Accepted equal-type questions have exactly equal parsed answers. -/
theorem check_consistency {t : QuestionType PauliType ℓ}
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : check L X Z projectPauli D DP t t a b = true) : a = b := by
  simp only [check, Bool.and_eq_true, ↓reduceIte, decide_eq_true_eq] at h
  exact h.1.1.1.2
end
end MIPRE.Introspection.TypedPredicate

namespace MIPRE.Introspection.TypedPredicate
noncomputable section
open Classical
variable {PauliType PauliAnswer F ι A : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
/-- Accepted introspection/sample answers satisfy the original full CL relation. -/
theorem check_sampling (w : Bool) {y z : ι → F} {a b : A}
    (h : check L X Z projectPauli D DP (.inr (.introspect, w)) (.inr (.sample, w))
      (.pair y a) (.pair z b) = true) : y = (L w).eval z ∧ a = b := by
  simp [check, fits, directed, CLChecks.sampling] at h
  exact @of_decide_eq_true _ (Classical.propDecidable _) h
end
end MIPRE.Introspection.TypedPredicate

namespace MIPRE.Introspection.TypedPredicate
noncomputable section
open Classical
variable {PauliType PauliAnswer F ι A : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
/-- Acceptance also includes the auxiliary check with the players reversed. -/
theorem check_directed_reversed {t u : QuestionType PauliType ℓ}
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : check L X Z projectPauli D DP t u a b = true) :
    directed L X Z projectPauli D u t b a = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.2
end
end MIPRE.Introspection.TypedPredicate

namespace MIPRE.Introspection.TypeGraph
section
open QuestionType Finset
set_option linter.unusedSectionVars false
variable {PauliType : Type*} [DecidableEq PauliType] {ℓ : ℕ}
/-- Pauli-Z connects to each Sample type. -/
theorem adj_pauliZ_sample (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (w : Bool) : adj (ℓ := ℓ) E X Z (pauli Z) (sample w) = true := by simp [adj, oriented]
end
end MIPRE.Introspection.TypeGraph

namespace MIPRE.Introspection.TypeGraph
section
open QuestionType Finset
set_option linter.unusedSectionVars false
variable {PauliType : Type*} [DecidableEq PauliType] {ℓ : ℕ}
/-- Each Sample type is checked against the corresponding introspection. -/
theorem adj_sample_introspect (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (w : Bool) : adj (ℓ := ℓ) E X Z (sample w) (introspect w) = true := by simp [adj, oriented]
end
end MIPRE.Introspection.TypeGraph

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

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {PauliType κ A B C H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Fintype κ] [DecidableEq κ] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  {ℓ : ℕ}
theorem aux_pauli_agreement_estimate (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      CL.Detyping.Question (QuestionType PauliType ℓ) κ → A → B → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM A H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM B K)
    {ε : ℝ} (hfail : 1 - povmValue (TypedPresentation.game E X Z ℓ P D) ψ MA MB ≤ ε)
    (t : AuxType ℓ) (w : Bool) (p : PauliType) (q : κ → ZMod 2)
    (hq : ∀ z, (P p).eval z = q) (hedge : TypeGraph.Adj E X Z (.inr (t, w)) (.inl p))
    (f : A → C) (g : B → C)
    (hcheck : ∀ a b, D (.inr (t, w), 0) (.inl p, q) a b = true → f a = g b) :
    (∑ z, xSqNorm ψ ((((MA (.inr (t, w), 0)).map f).mats z).val)
      ((((MB (.inl p, q)).map g).mats z).val)) ≤
        2 * (TypeGraph.edges E X Z ℓ).card * ε :=
  constant_edge_agreement_estimate E X Z P D ψ hψ MA MB hfail (.inr (t, w)) (.inl p) 0 q
    (TypedPresentation.eval_aux P t w) hq hedge f g hcheck
end
end MIPRE.Introspection.TypedEstimates

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

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι A H K : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
/-- The actual reversed Z/Sample edge compares the sampled seed with Bob's
projected Pauli answer; wrong constructors cannot be accepted. -/
theorem check_sample_pauliZ_seed (w : Bool)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.sample w) (QuestionType.pauli Z) a b = true) :
    sampleSeed a = pauliProjection projectPauli b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i z a b
  have hd := TypedPredicate.check_directed_reversed L X Z projectPauli D DP h
  simp only [TypedPredicate.directed, ↓reduceIte] at hd
  have he : projectPauli b = z := of_decide_eq_true hd
  exact congrArg some he.symm
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {H K Y : Type*} [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y]
/-- Replacing Bob's tested observable by its extracted ideal observable. -/
theorem sampling_replace_bob (ψ : H × K → ℂ)
    (S : Y → Matrix H H ℂ) (Z Q : Y → Matrix K K ℂ) {e η : ℝ}
    (hS : ∑ y, xSqNorm ψ (S y) (Z y) ≤ e)
    (hZ : ∑ y, snorm ψ (bOp (Z y - Q y)) ^ 2 ≤ η) :
    ∑ y, xSqNorm ψ (S y) (Q y) ≤ 2 * e + 2 * η := by
  have ht := sum_snorm_sq_triangle' ψ (fun y => aOp (S y))
    (fun y => bOp (Z y)) (fun y => bOp (Q y))
  simp only [← bOp_sub, ← xSqNorm_eq_snorm_sq] at ht
  linarith only [ht, hS, hZ]
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
/-- An ideal mirror identifies same-side replacement error with fine
cross-party consistency, before any coarse-graining is performed. -/
theorem xSqNorm_eq_stateSqNorm_of_mirror
    {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (ψ : H × K → ℂ) (M P : Matrix H H ℂ) (Q : Matrix K K ℂ)
    (hmirror : aOp P *ᵥ ψ = bOp Q *ᵥ ψ) :
    xSqNorm ψ M Q = stateSqNorm ψ (P - M) := by
  calc
    _ = snorm ψ (bOp Q - aOp M) ^ 2 := by rw [xSqNorm_eq_snorm_sq, snorm_sub_comm]
    _ = snorm ψ (aOp P - aOp M) ^ 2 := by simp only [snorm, Matrix.sub_mulVec, hmirror]
    _ = _ := by rw [stateSqNorm, stateNorm, norm_stateVec_eq_snorm, aOp_sub]
end
end MIPRE.Introspection

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K C : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PauliAnswer]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype C] [DecidableEq C]
theorem sampleJointZ_left (P : CL.CLFun F ι ℓ) (g : (ι → F) → C)
    (M : POVM (ParsedAnswer (ι → F) A PauliAnswer) H) (y : Option ((ι → F) × A)) :
    (∑ c, ((M.map (sampleJointZ P g)).mats (y, c)).val) =
      ((M.map (evaluatedSamplePair P)).mats y).val := by
  have hm := POVM.sum_mats_map_prod M (evaluatedSamplePair P) (sampledCoarseZ g) y
  convert hm using 1
  apply Finset.sum_congr rfl
  intro c _
  unfold sampleJointZ
  simp only [POVM.map_mats, Finset.sum_filter]
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K C : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PauliAnswer]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype C] [DecidableEq C]
theorem sampleJointZ_right (P : CL.CLFun F ι ℓ) (g : (ι → F) → C)
    (M : POVM (ParsedAnswer (ι → F) A PauliAnswer) H) (c : Option C) :
    (∑ y, ((M.map (sampleJointZ P g)).mats (y, c)).val) =
      ((M.map (sampledCoarseZ g)).mats c).val := by
  have hm := POVM.sum_mats_map_prod_prime M (evaluatedSamplePair P) (sampledCoarseZ g) c
  convert hm using 1
  apply Finset.sum_congr rfl
  intro y _
  unfold sampleJointZ
  simp only [POVM.map_mats, Finset.sum_filter]
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K C : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PauliAnswer]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype C] [DecidableEq C]
theorem sampledCoarseZ_mapped (g : (ι → F) → C)
    (M : POVM (ParsedAnswer (ι → F) A PauliAnswer) H) (c : Option C) :
    fibSum (fun z => ((M.map sampleSeed).mats z).val) (Option.map g) c =
      ((M.map (sampledCoarseZ g)).mats c).val := by
  rw [fibSum, ← POVM.map_mats, POVM.map_map]
  rfl
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K C : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PauliAnswer]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype C] [DecidableEq C]
/-- Ideal Z followed by any classical seed processing is the corresponding
computational readout on the same register. -/
theorem idealZ_coarse_fibSum (g : (ι → F) → C) (c : Option C) :
    fibSum (fun z => (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
      Matrix ((ι → F) × K) _ ℂ)) (Option.map g) c =
      aOp (readout (fun z => some (g z)) c) := by
  rw [fibSum_aOp, fibSum_readout]
  rfl
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K C : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PauliAnswer]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype C] [DecidableEq C]
variable [Fintype PauliType] [DecidableEq PauliType] [Fintype κ] [DecidableEq κ]
variable [Algebra (ZMod 2) F]
/-- Every computational seed readout has an exact mirror on the extracted
EPR register, including with arbitrary auxiliary state. -/
theorem coarseZ_registerState_mirror (g : (ι → F) → C) (c : C) (ξ : H × K → ℂ) :
    aOp (aOp (readout g c) : Matrix ((ι → F) × H) _ ℂ) *ᵥ registerState (ι → F) ξ =
      bOp (aOp (readout g c) : Matrix ((ι → F) × K) _ ℂ) *ᵥ registerState (ι → F) ξ := by
  have he := Weyl.stateVec_epr (readout g c)
  have ht : (readout g c)ᵀ = readout g c := Matrix.diagonal_transpose _
  rw [ht, ← registerEPR_eq_weyl] at he
  exact congrArg WithLp.ofLp (mirror_expVec (registerEPR (ι → F)) ξ _ _ he)
end
end MIPRE.Introspection.TypedEstimates

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K C : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PauliAnswer]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype C] [DecidableEq C]
variable [Fintype PauliType] [DecidableEq PauliType] [Fintype κ] [DecidableEq κ]
variable [Algebra (ZMod 2) F]
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
    (g : (ι → F) → C) :
    (∑ a, ∑ c, stateSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val *
        (aOp (readout (fun z => some (g z)) c) : Matrix ((ι → F) × H) _ ℂ) -
       (aOp (readout (fun z => some (g z)) c) : Matrix ((ι → F) × H) _ ℂ) *
        (((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val)) ≤
      64 * η + 224 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hψ : star (registerState (ι → F) ξ) ⬝ᵥ registerState (ι → F) ξ = 1 := by
    rw [dotProduct_star_self, registerState_norm ξ (norm_evec_eq_one_of_unit hξ)]
    norm_num
  have hsample := aux_pauli_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (registerState (ι → F) ξ) hψ MA MB hfail
    .sample w Z q hq
    (TypeGraph.symmetric E X Z _ _ (TypeGraph.adj_pauliZ_sample E X Z w))
    sampleSeed (pauliProjection projectPauli)
    (fun a b hab => check_sample_pauliZ_seed L X Z projectPauli D
      (fun p s => DP p s 0 q) w hab)
  have hseed := sampling_replace_bob (registerState (ι → F) ξ)
    (fun z => (((MA (QuestionType.sample w, 0)).map sampleSeed).mats z).val)
    (fun z => (((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val)
    (fun z => (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
      Matrix ((ι → F) × K) _ ℂ)) hsample hZ
  have hdist := hseed
  simp only [xSqNorm_eq_stateSqNorm_of_mirror _ _ _ _
    (coarseZ_registerState_mirror (some : (ι → F) → Option (ι → F)) _ ξ)] at hdist
  have hloop := aux_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (registerState (ι → F) ξ) hψ MA MB hfail
    .sample .sample w w (TypeGraph.adj_self E X Z (QuestionType.sample w))
    sampleSeed sampleSeed (fun a b hab => congrArg sampleSeed
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have hseedB := sum_xSqNorm_le_of_two_step
    (fun z => (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
      Matrix ((ι → F) × H) _ ℂ))
    (fun z => (((MA (QuestionType.sample w, 0)).map sampleSeed).mats z).val)
    (fun z => (((MB (QuestionType.sample w, 0)).map sampleSeed).mats z).val) hdist hloop
  have hcoarse := sum_xSqNorm_fibSum_le (norm_evec_eq_one_of_unit hψ)
    (readout_isPVM (some : (ι → F) → Option (ι → F))).aOp
    (isPVM_povm_map (MB (QuestionType.sample w, 0)) hS sampleSeed) (Option.map g)
  simp only [sampledCoarseZ_mapped, idealZ_coarse_fibSum] at hcoarse
  have hright := hcoarse.trans hseedB
  have hleft := aux_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (registerState (ι → F) ξ) hψ MA MB hfail
    .introspect .sample w w
    (TypeGraph.symmetric E X Z _ _ (TypeGraph.adj_sample_introspect E X Z w))
    introspectPair (evaluatedSamplePair (L w)) (fun a b hab => by
      have hf := TypedPredicate.check_formats L X Z projectPauli D (fun p s => DP p s 0 0) hab
      cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
      rename_i y a z b
      have he := TypedPredicate.check_sampling L X Z projectPauli D
        (fun p s => DP p s 0 0) w hab
      exact congrArg some (Prod.ext he.1 he.2))
  let N : POVM (Option C) ((ι → F) × H) :=
    (IsPVM.aOp (dB := H) (readout_isPVM (fun z : ι → F => some (g z)))).toPOVM
  have ht := coarse_joint_commutator_bound (registerState (ι → F) ξ)
    ((MA (QuestionType.introspect w, 0)).map introspectPair) N
    (MB (QuestionType.sample w, 0)) hS (sampleJointZ (L w) g)
  simp only [coarseJointLeftError, coarseJointRightError, sampleJointZ_left,
    sampleJointZ_right, N, IsPVM.toPOVM_mats] at ht
  linarith only [ht, hleft, hright]
end MIPRE.Introspection.TypedEstimates

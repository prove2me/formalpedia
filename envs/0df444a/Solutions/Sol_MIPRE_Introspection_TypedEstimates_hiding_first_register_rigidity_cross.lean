-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.hiding_first_register_rigidity_cross
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:44:29.231929+00:00
-- url     : https://prove2.me/submissions/bd1cff3e-48ae-4f47-8087-6397a5fdb14b

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HidingBaseRigidity.lean (solution of MIPRE.Introspection.TypedEstimates.hiding_first_register_rigidity_cross);
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
import Definitions.Def_MIPRE_Foundations_Introspection_PauliAuxEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingBaseOperators
import Definitions.Def_MIPRE_Foundations_Introspection_HidingNormalizerPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidityOrientation
import Theorems.Thm_MIPRE_Introspection_Honest_hideRegister_transpose
import Theorems.Thm_MIPRE_Introspection_Honest_pauliXReadout_firstHide
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_constant_edge_agreement_estimate
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_POVM_map_map
import Theorems.Thm_MIPRE_Weyl_epr_unit
import Theorems.Thm_MIPRE_Weyl_isPVM_synOf
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wX
import Theorems.Thm_MIPRE_Weyl_stateVec_epr
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_mulVec_kron_kron_expVec
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
theorem snorm_sub_comm (M M' : Matrix N N ℂ) : snorm v (M - M') = snorm v (M' - M) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, evec_sub, evec_sub, norm_sub_rev]
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
/-- The expanded state's norm splits, so it is a unit vector when both factors are. -/
theorem expVec_dotProduct (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) :
    star (expVec ψ e) ⬝ᵥ expVec ψ e = (star ψ ⬝ᵥ ψ) * (star e ⬝ᵥ e) := by
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
theorem expVec_unit {ψ : dA × dB → ℂ} {e : anc × anc' → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (he : star e ⬝ᵥ e = 1) : star (expVec ψ e) ⬝ᵥ expVec ψ e = 1 := by
  rw [expVec_dotProduct, hψ, he, mul_one]
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
/-- Acceptance includes the auxiliary check in the displayed player order. -/
theorem check_directed {t u : QuestionType PauliType ℓ}
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : check L X Z projectPauli D DP t u a b = true) :
    directed L X Z projectPauli D t u a b = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.1.2
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
/-- The Pauli-X/hiding-first edge checks the dual first register and the untouched tail. -/
theorem check_hiding_pauli (w : Bool) (k : Fin ℓ) (hk : k.val = 0)
    {a : PauliAnswer} {y yp x : ι → F}
    (h : check L X Z projectPauli D DP (.inl X) (.inr (.hide k, w))
      (.pauli a) (.hide y yp x) = true) :
    CLChecks.hidingPauli (L w) (projectPauli a) (y, yp, x) := by
  have hd := check_directed L X Z projectPauli D DP h
  simp only [directed, hk, and_self, ↓reduceIte] at hd
  exact @of_decide_eq_true _ (Classical.propDecidable _) hd
end
end MIPRE.Introspection.TypedPredicate

namespace MIPRE.Introspection.TypeGraph
section
open QuestionType Finset
set_option linter.unusedSectionVars false
variable {PauliType : Type*} [DecidableEq PauliType] {ℓ : ℕ}
/-- The Pauli-X vertex starts both hiding chains. -/
theorem adj_pauliX_hide_first (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (hℓ : 0 < ℓ) (w : Bool) : adj E X Z (pauli X) (hide w ⟨0, hℓ⟩) = true := by
  simp [adj, oriented]
end
end MIPRE.Introspection.TypeGraph

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hideOp_transpose (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (a : HideLabel F ι) : (hideOp P k h a)ᵀ = hideOp P k h a := by
  change registerOp univRestriction (hideRegister P k univ h a)ᵀ = _
  rw [hideRegister_transpose]
  rfl
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hideCoarseOp_transpose (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (i : Option (HideLabel F ι)) :
    (hideCoarseOp P k h i)ᵀ = hideCoarseOp P k h i := by
  rw [hideCoarseOp, fibSum, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun a _ => hideOp_transpose P k h a
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hideCoarseOp_epr_mirror (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (i : Option (HideLabel F ι)) :
    aOp (hideCoarseOp P k h i) *ᵥ registerEPR (ι → F) =
      bOp (hideCoarseOp P k h i) *ᵥ registerEPR (ι → F) := by
  have he := stateVec_epr (hideCoarseOp P k h i)
  rw [hideCoarseOp_transpose, ← registerEPR_eq_weyl] at he
  exact congrArg WithLp.ofLp he
end
end MIPRE.Introspection.Honest

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

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PauliAnswer H K : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype PauliAnswer]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
/-- Exact ideal mirrors persist with any bipartite auxiliary state. -/
theorem hideCoarseOp_registerState_mirror (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (ξ : H × K → ℂ) (i : Option (HideLabel F ι)) :
    aOp (aOp (hideCoarseOp P k h i) : Matrix ((ι → F) × H) _ ℂ) *ᵥ registerState (ι → F) ξ =
      bOp (aOp (hideCoarseOp P k h i) : Matrix ((ι → F) × K) _ ℂ) *ᵥ
        registerState (ι → F) ξ := by
  have he := mirror_expVec (registerEPR (ι → F)) ξ (hideCoarseOp P k h i)
    (hideCoarseOp P k h i) (congrArg evec (hideCoarseOp_epr_mirror P k h i))
  exact congrArg WithLp.ofLp he
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {PauliType κ A B C H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Fintype κ] [DecidableEq κ] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  {ℓ : ℕ}
theorem pauli_aux_agreement_estimate (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      CL.Detyping.Question (QuestionType PauliType ℓ) κ → A → B → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM A H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM B K)
    {ε : ℝ} (hfail : 1 - povmValue (TypedPresentation.game E X Z ℓ P D) ψ MA MB ≤ ε)
    (p : PauliType) (q : κ → ZMod 2) (hq : ∀ z, (P p).eval z = q)
    (t : AuxType ℓ) (w : Bool) (hedge : TypeGraph.Adj E X Z (.inl p) (.inr (t, w)))
    (f : A → C) (g : B → C)
    (hcheck : ∀ a b, D (.inl p, q) (.inr (t, w), 0) a b = true → f a = g b) :
    (∑ z, xSqNorm ψ ((((MA (.inl p, q)).map f).mats z).val)
      ((((MB (.inr (t, w), 0)).map g).mats z).val)) ≤
        2 * (TypeGraph.edges E X Z ℓ).card * ε :=
  constant_edge_agreement_estimate E X Z P D ψ hψ MA MB hfail (.inl p) (.inr (t, w)) q 0 hq
    (TypedPresentation.eval_aux P t w) hedge f g hcheck
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

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem hidingCoarse_zero_hide (P : CL.CLFun F ι ℓ) (y yp x : ι → F) :
    hidingCoarse (A := A) (PauliAnswer := PauliAnswer) P 0 (.hide y yp x) =
      some (0, CL.proj (P.factorOfPrefix 0 0) yp, CL.proj (P.factorOfPrefix 0 0)ᶜ x) := by
  have hr : CLChecks.prefixRegister P 1 y = P.factorOfPrefix 0 0 := by
    cases P <;> simp [CLChecks.prefixRegister]
  simp only [hidingCoarse, CL.CLFun.outputPrefix_zero, hr]
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
/-- This implication is over the complete parsed alphabet; acceptance excludes
every malformed constructor before the Pauli-X comparison is used. -/
theorem hiding_first_accepts
    (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (w : Bool) (k : Fin ℓ) (hk : k.val = 0)
    (a b : ParsedAnswer (ι → F) A PauliAnswer)
    (hab : TypedPredicate.check L X Z projectPauli D DP (.inl X)
      (.inr (.hide k, w)) a b = true) :
    Option.map (Honest.firstHideAnswer (L w)) (pauliProjection projectPauli a) =
      hidingCoarse (L w) 0 b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP hab
  cases a <;> cases b <;> simp only [TypedPredicate.fits, Bool.false_eq_true, and_false,
    false_and] at hf
  rename_i a y yp x
  have hc := TypedPredicate.check_hiding_pauli L X Z projectPauli D DP w k hk hab
  rw [pauliProjection, Option.map_some, hidingCoarse_zero_hide]
  exact congrArg some (Prod.ext rfl (Prod.ext hc.1.symm hc.2))
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
/-- Actual game failure controls the first hiding coarse family against the
tested coarse Pauli-X family, on either player's full local carrier. -/
theorem hiding_first_agreement_estimate
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K)
    {ε : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)
    (w : Bool) (k : Fin ℓ) (hk : k.val = 0)
    (qX : κ → ZMod 2) (hqX : ∀ z, (P X).eval z = qX) :
    (∑ z, xSqNorm ψ
      ((((MA (.inl X, qX)).map (fun a =>
        Option.map (Honest.firstHideAnswer (L w)) (pauliProjection projectPauli a))).mats z).val)
      ((((MB (QuestionType.hide w k, 0)).map (hidingCoarse (L w) 0)).mats z).val)) ≤
        2 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hℓ : 0 < ℓ := by simpa only [hk] using k.isLt
  have heq : k = ⟨0, hℓ⟩ := Fin.ext hk
  have hedge : TypeGraph.Adj E X Z (.inl X) (.inr (.hide k, w)) := by
    subst k
    exact TypeGraph.adj_pauliX_hide_first E X Z hℓ w
  exact pauli_aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    ψ hψ MA MB hfail X qX hqX (.hide k) w hedge
    (fun a => Option.map (Honest.firstHideAnswer (L w)) (pauliProjection projectPauli a))
    (hidingCoarse (L w) 0)
    (hiding_first_accepts L X Z projectPauli D (fun p r => DP p r qX 0) w k hk)
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem pauliX_firstHide_mapped (P : CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (M : POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (z : Option (Honest.HideLabel F ι)) :
    fibSum (fun x => ((M.map (pauliProjection projectPauli)).mats x).val)
      (Option.map (Honest.firstHideAnswer P)) z =
      ((M.map (fun a => Option.map (Honest.firstHideAnswer P)
        (pauliProjection projectPauli a))).mats z).val := by
  rw [fibSum, ← POVM.map_mats, POVM.map_map]
end
end MIPRE.Introspection.TypedEstimates

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
variable
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
  {ε : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
    (registerState (ι → F) ξ) MA MB ≤ ε)
include hξ hfail
theorem _root_.solution
    (w : Bool) (k : Fin ℓ) (hk : k.val = 0) (hL : (L w).SupportedOn univ)
    (qX : κ → ZMod 2) (hqX : ∀ z, (P X).eval z = qX)
    (hMA : IsPVM (fun a => ((MA (.inl X, qX)).mats a).val)) {δX : ℝ}
    (hPauli : ∑ x, xSqNorm (registerState (ι → F) ξ)
      ((((MA (.inl X, qX)).map (pauliProjection projectPauli)).mats x).val)
      (aOp (Honest.pauliXReadout x) : Matrix ((ι → F) × K) _ ℂ) ≤ δX) :
    hidingBobError L w hL ξ MB k ≤ 4 * (TypeGraph.edges E X Z ℓ).card * ε + 2 * δX := by
  have hseed : star (registerEPR (ι → F)) ⬝ᵥ registerEPR (ι → F) = 1 := by
    rw [registerEPR_eq_weyl]
    exact Weyl.epr_unit
  have hunit := expVec_unit hseed hξ
  have hcoarse := sum_xSqNorm_fibSum_le (norm_evec_eq_one_of_unit hunit)
    (isPVM_povm_map (MA (.inl X, qX)) hMA (pauliProjection projectPauli))
    (Honest.pauliXReadout_isPVM (F := F) (ι := ι)).aOp
    (Option.map (Honest.firstHideAnswer (L w)))
  have hc := hcoarse.trans hPauli
  simp only [pauliX_firstHide_mapped, fibSum_aOp, Honest.pauliXReadout_firstHide (L w) hL] at hc
  have htest := hiding_first_agreement_estimate E X Z P L projectPauli D DP
    (registerState (ι → F) ξ) hunit MA MB hfail w k hk qX hqX
  let M := (MA (.inl X, qX)).map (fun a =>
    Option.map (Honest.firstHideAnswer (L w)) (pauliProjection projectPauli a))
  have hc' : ∑ z, stateSqNorm (registerState (ι → F) ξ)
      ((aOp (Honest.hideCoarseOp (L w) 0 hL z) : Matrix ((ι → F) × H) _ ℂ) -
        (M.mats z).val) ≤ δX := by
    calc
      _ = ∑ z, xSqNorm (registerState (ι → F) ξ) (M.mats z).val
          (aOp (Honest.hideCoarseOp (L w) 0 hL z) : Matrix ((ι → F) × K) _ ℂ) := by
        apply Finset.sum_congr rfl
        intro z _
        exact (xSqNorm_eq_stateSqNorm_of_mirror _ _ _ _
          (Honest.hideCoarseOp_registerState_mirror (L w) 0 hL ξ z)).symm
      _ ≤ δX := hc
  have ht := sum_xSqNorm_le_of_two_step
    (fun z => (aOp (Honest.hideCoarseOp (L w) 0 hL z) : Matrix ((ι → F) × H) _ ℂ))
    (fun z => (M.mats z).val)
    (fun z => (((MB (QuestionType.hide w k, 0)).map (hidingCoarse (L w) 0)).mats z).val)
    hc' htest
  simpa only [hidingBobError, hk] using ht.trans_eq (by ring)
end MIPRE.Introspection.TypedEstimates

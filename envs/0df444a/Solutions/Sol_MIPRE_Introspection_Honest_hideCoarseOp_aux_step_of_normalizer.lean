-- Prove2me | solution 1 for MIPRE.Introspection.Honest.hideCoarseOp_aux_step_of_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:53:35.775862+00:00
-- url     : https://prove2.me/submissions/c1a006ae-92f1-4b80-b7b6-bde938052154

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ConditionalNormalizerStepAux.lean (solution of MIPRE.Introspection.Honest.hideCoarseOp_aux_step_of_normalizer);
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
import Theorems.Thm_MIPRE_Introspection_Honest_coarseOp_comp
import Theorems.Thm_MIPRE_Introspection_Honest_hideOp_conditionalIdeal_eq_next
import Theorems.Thm_MIPRE_Introspection_Honest_hideRegister_commute_next
import Theorems.Thm_MIPRE_Introspection_Honest_hideRegister_marginal
import Theorems.Thm_MIPRE_Introspection_Honest_hideRegister_transpose
import Theorems.Thm_MIPRE_Introspection_linear_measurement_isPVM
import Theorems.Thm_MIPRE_Introspection_linear_measurements_commute
import Theorems.Thm_MIPRE_Introspection_readout_isPVM
import Theorems.Thm_MIPRE_Introspection_registerOp_isPVM
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_POVM_map_map
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wX
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wZ
import Theorems.Thm_MIPRE_Weyl_proj_mul_proj
import Theorems.Thm_MIPRE_Weyl_stateVec_epr
import Theorems.Thm_MIPRE_Weyl_sum_proj
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_mulVec_kron_kron_expVec
import Theorems.Thm_MIPRE_norm_evec_expVec
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_eq
import Theorems.Thm_MIPRE_star_sgn
import Theorems.Thm_MIPRE_sum_bornProb_le_fibSum
import Theorems.Thm_MIPRE_sum_kronecker_left

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_comm (x y : Fin n → F) : dotForm F n x y = dotForm F n y x := by
  simp only [dotForm_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_isRefl : (dotForm F n).IsRefl := fun x y h => by
  rw [dotForm_comm]; exact h
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_nondegenerate : (dotForm F n).Nondegenerate := by
  have key : ∀ x : Fin n → F, ∀ i : Fin n,
      dotForm F n x (Pi.single i 1) = x i := by
    intro x i
    rw [dotForm_apply, Finset.sum_eq_single i
      (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ i) h)]
    simp
  refine ⟨fun x hx => funext fun i => ?_, fun y hy => funext fun i => ?_⟩
  · rw [← key x i]; exact hx _
  · rw [← key y i, dotForm_comm]; exact hy _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
/-- **`lem:perp_perp`**, second part: the dot-product perp is an involution on subspaces, over
every field. -/
theorem perp_perp (S : Submodule F (Fin n → F)) : perp (perp S) = S :=
  LinearMap.BilinForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_isRefl S
end
end MIPRE.CL

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
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_mul (X Y : Matrix HB HB ℂ) :
    bOp (X * Y) = (bOp X : Matrix (HA × HB) _ ℂ) * bOp Y := by
  rw [bOp, bOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
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
/-- **The two factors commute.** -/
theorem aOp_mul_bOp (X : Matrix HA HA ℂ) (Y : Matrix HB HB ℂ) :
    (aOp X : Matrix (HA × HB) _ ℂ) * bOp Y = bOp Y * aOp X := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
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
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bOp_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix dB dB ℂ) :
    bOp (∑ i ∈ s, f i) = ∑ i ∈ s, (bOp (f i) : Matrix (dA × dB) _ ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, bOp, Matrix.kronecker_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, bOp_add, ih, Finset.sum_insert hi]
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

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The defining Fourier average, as a rewrite. -/
theorem proj_def (w : (n → F) → Matrix (n → F) (n → F) ℂ) (e : n → F) :
    proj w e = (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • w a := rfl
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
/-- The projectors are self-adjoint. -/
theorem proj_conjTranspose (hw : IsWeylFamily w) (e : n → F) : (proj w e)ᴴ = proj w e := by
  classical
  rw [proj_def w e, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [Matrix.conjTranspose_smul, hw.selfAdjoint a, star_sgn]]
  congr 1
  simp
end
end MIPRE.Weyl

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
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
/-- Jointly reading two commuting projective measurements gives a projective measurement. -/
theorem joint_measurement_isPVM {ι A B : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (P : A → Matrix ι ι ℂ) (Q : B → Matrix ι ι ℂ) (hP : IsPVM P) (hQ : IsPVM Q)
    (hc : ∀ a b, Commute (P a) (Q b)) : IsPVM (fun ab : A × B => P ab.1 * Q ab.2) where
  isSelfAdjoint ab := by
    rw [Matrix.conjTranspose_mul, hP.isSelfAdjoint, hQ.isSelfAdjoint]
    exact (hc ab.1 ab.2).eq.symm
  idem ab := by
    rw [mul_assoc, ← mul_assoc (Q ab.2), (hc ab.1 ab.2).eq.symm,
      mul_assoc (P ab.1), hQ.idem, ← mul_assoc, hP.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hQ.sum_eq_one, mul_one]
    exact hP.sum_eq_one
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
/-- The sampling and hiding readouts used by the honest introspection strategy form a PVM. -/
theorem sampling_hiding_isPVM
    (L R : (Fin n → F) →ₗ[F] (Fin n → F)) (hLR : CL.perp R.ker ≤ L.ker) :
    IsPVM (fun ab : (Fin n → F) × (Fin n → F) => synOf wZ L ab.1 * synOf wX R ab.2) :=
  joint_measurement_isPVM _ _ (linear_measurement_isPVM wZ isWeylFamily_wZ L)
    (linear_measurement_isPVM wX isWeylFamily_wX R) (linear_measurements_commute L R hLR)
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

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K I Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]
theorem commute_fibSum_right (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (hc : ∀ y i, Commute (Q y) (P i)) (f : I → Z) (y : Y) (z : Z) :
    Commute (Q y) (fibSum P f z) := by
  apply Commute.sum_right
  intro i _
  exact hc y i
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K I Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]
/-- Conditional ideal outcomes form a complete PVM although their coarse maps vary. -/
theorem conditionalIdeal_isPVM (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (f : Y → I → Z) (hP : IsPVM P) (hQ : IsPVM Q)
    (hc : ∀ y i, Commute (Q y) (P i)) : IsPVM (conditionalIdeal P Q f) where
  isSelfAdjoint p :=
    (joint_measurement_isPVM Q (fibSum P (f p.1)) hQ (isPVM_fibSum hP _)
      (commute_fibSum_right P Q hc _)).isSelfAdjoint p
  idem p :=
    (joint_measurement_isPVM Q (fibSum P (f p.1)) hQ (isPVM_fibSum hP _)
      (commute_fibSum_right P Q hc _)).idem p
  sum_eq_one := by
    simp only [conditionalIdeal, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (isPVM_fibSum hP _).sum_eq_one, mul_one]
    exact hQ.sum_eq_one
end
end MIPRE.Introspection

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]
theorem adaptiveTensor_isPVM (P : A → Matrix I I ℂ) (Q : A → B → Matrix J J ℂ)
    (hP : IsPVM P) (hQ : ∀ a, IsPVM (Q a)) : IsPVM (adaptiveTensor P Q) where
  isSelfAdjoint ab := by
    simp only [adaptiveTensor, Matrix.conjTranspose_kronecker,
      hP.isSelfAdjoint, (hQ _).isSelfAdjoint]
  idem ab := by
    simp only [adaptiveTensor, ← Matrix.mul_kronecker_mul, hP.idem, (hQ _).idem]
  sum_eq_one := by
    simp only [adaptiveTensor, Fintype.sum_prod_type]
    simp_rw [← kronecker_sum_right, (hQ _).sum_eq_one]
    rw [← sum_kronecker_left, hP.sum_eq_one, Matrix.one_kronecker_one]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem localRead_isPVM {S : Finset ι} (L : CL.RegLinear F S) : IsPVM (localRead L) := by
  apply sampling_hiding_isPVM
  simp only [CL.ker_lperp, CL.perp_perp]
  exact le_rfl
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem stopHide_isPVM {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (V : Finset ι) :
    IsPVM (stopHide P V) := by
  have hX : IsPVM (proj (wX (F := F) (n := V))) :=
    ⟨proj_conjTranspose isWeylFamily_wX,
      fun x => by rw [proj_mul_proj isWeylFamily_wX, if_pos rfl], sum_proj isWeylFamily_wX⟩
  exact hX.coarse (stopHideAnswer P V)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
/-- Projectivity of every honest hiding level, including the branch-dependent later levels. -/
theorem hideRegister_isPVM {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (V : Finset ι) (h : P.SupportedOn V) : IsPVM (hideRegister P k V h) := by
  induction P generalizing V k with
  | zero => cases k <;> exact stopHide_isPVM _ _
  | cons S L next ih =>
      cases k with
      | zero => exact stopHide_isPVM _ _
      | succ k =>
          exact registerOp_isPVM (coordinateSplit S V h.1)
            ((adaptiveTensor_isPVM (localRead L) _ (localRead_isPVM L)
              (fun z => ih _ _ _ (h.2 _))).coarse (joinHide S))
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem hideOp_isPVM {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn Finset.univ) : IsPVM (hideOp P k h) :=
  registerOp_isPVM _ (hideRegister_isPVM P k _ h)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem hideOp_marginal {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn Finset.univ) (y : ι → F) :
    (∑ yp : (ι → F) × (ι → F), hideOp P k h (y, yp)) = readout (P.truncate k).eval y := by
  unfold hideOp
  rw [← registerOp_sum, hideRegister_marginal]
  ext x x'
  simp [readout, registerOp_apply, Matrix.diagonal_apply]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B C U V : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
theorem registerOp_commute (e : I ≃ J) {P Q : Matrix J J ℂ} (hc : Commute P Q) :
    Commute (registerOp e P) (registerOp e Q) := by
  show _ * _ = _ * _
  rw [← registerOp_mul, ← registerOp_mul, hc.eq]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hideOp_commute_next (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn Finset.univ) (a b : HideLabel F ι) :
    Commute (hideOp P k h a) (hideOp P (k + 1) h b) :=
  registerOp_commute _ (hideRegister_commute_next P k _ h a b)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hidingPrefixOp_isPVM (P : CL.CLFun F ι ℓ) (k : ℕ) :
    IsPVM (hidingPrefixOp P k) := readout_isPVM _
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The next ideal Z prefix commutes with every actual preceding honest Hide
operator, including prefixes whose readout projector is zero. -/
theorem hidingPrefixOp_commute_hideOp (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (y : Option (ι → F)) (a : HideLabel F ι) :
    Commute (hidingPrefixOp P (k + 1) y) (hideOp P k h a) := by
  cases y with
  | none => rw [hidingPrefixOp_none]; exact Commute.zero_left _
  | some y =>
    rw [hidingPrefixOp_some, ← hideOp_marginal P (k + 1) h y]
    apply Commute.sum_left
    intro b _
    exact (hideOp_commute_next P k h a (y, b)).symm
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The same explicit prefix commutes with any coarse family of the preceding
honest hiding measurement. This applies to the retained fine label in the
soundness induction. -/
theorem hidingPrefixOp_commute_coarse (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) {J : Type*} [Fintype J] [DecidableEq J]
    (f : HideLabel F ι → J) (y : Option (ι → F)) (j : J) :
    Commute (hidingPrefixOp P (k + 1) y) (fibSum (hideOp P k h) f j) :=
  commute_fibSum_right (hideOp P k h) (hidingPrefixOp P (k + 1))
    (hidingPrefixOp_commute_hideOp P k h) f y j
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hideCoarseOp_isPVM (P : CL.CLFun F ι ℓ) (k : ℕ) (h : P.SupportedOn univ) :
    IsPVM (hideCoarseOp P k h) := isPVM_fibSum (hideOp_isPVM P k h) _
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false in
/-- The guarded conditional ideal formed from the actual retained fine
family is exactly the next honest test-coarse measurement. -/
theorem hideCoarseOp_conditionalIdeal_eq_next (P : CL.CLFun F ι ℓ) (k : ℕ)
    (hk : k + 1 < ℓ) (h : P.SupportedOn univ)
    (p : Option (ι → F) × Option (HideLabel F ι)) :
    conditionalIdeal (hideCoarseOp P k h) (hidingPrefixOp P (k + 1))
      (TypedEstimates.hidingNextGuarded P k) p =
        fibSum (hideOp P (k + 1) h) (hideLabelNext P k) p := by
  have hc := coarseOp_comp (hideLabelCoarse P k)
    (TypedEstimates.hidingNextGuarded P k p.1) (hideOp P k h) p.2
  change fibSum (hideCoarseOp P k h) (TypedEstimates.hidingNextGuarded P k p.1) p.2 =
    fibSum (hideOp P k h)
      (fun a => TypedEstimates.hidingNextGuarded P k p.1 (hideLabelCoarse P k a)) p.2 at hc
  rw [conditionalIdeal, hc]
  exact hideOp_conditionalIdeal_eq_next P k hk h p
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the redundant conditioning bookkeeping yields precisely the
next fine ideal hiding family, ready for the next induction stage. -/
theorem hideCoarseOp_conditionalIdeal_step (P : CL.CLFun F ι ℓ) (k : ℕ)
    (hk : k + 1 < ℓ) (h : P.SupportedOn univ) (z : Option (HideLabel F ι)) :
    fibSum (conditionalIdeal (hideCoarseOp P k h) (hidingPrefixOp P (k + 1))
      (TypedEstimates.hidingNextGuarded P k)) hideNextRetain z =
        hideCoarseOp P (k + 1) h z := by
  have he : conditionalIdeal (hideCoarseOp P k h) (hidingPrefixOp P (k + 1))
      (TypedEstimates.hidingNextGuarded P k) =
        fibSum (hideOp P (k + 1) h) (hideLabelNext P k) :=
    funext (hideCoarseOp_conditionalIdeal_eq_next P k hk h)
  rw [he]
  exact coarseOp_comp (hideLabelNext P k) hideNextRetain (hideOp P (k + 1) h) z
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {H K I Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]
theorem fibSum_mirror (ψ : H × K → ℂ)
    (P : I → Matrix H H ℂ) (R : I → Matrix K K ℂ)
    (h : ∀ i, aOp (P i) *ᵥ ψ = bOp (R i) *ᵥ ψ) (f : I → Z) (z : Z) :
    aOp (fibSum P f z) *ᵥ ψ = bOp (fibSum R f z) *ᵥ ψ := by
  simp only [fibSum, aOp_sum, bOp_sum, Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun i _ => h i
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {H K I Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]
/-- Mirrors reverse multiplication order; commutation of the ideal prefix and
fine projectors restores the order defining the conditional ideal. -/
theorem conditionalIdeal_mirror (ψ : H × K → ℂ)
    (P : I → Matrix H H ℂ) (R : I → Matrix K K ℂ)
    (Q : Y → Matrix H H ℂ) (S : Y → Matrix K K ℂ) (f : Y → I → Z)
    (hP : ∀ i, aOp (P i) *ᵥ ψ = bOp (R i) *ᵥ ψ)
    (hQ : ∀ y, aOp (Q y) *ᵥ ψ = bOp (S y) *ᵥ ψ)
    (hc : ∀ y i, Commute (S y) (R i)) (p : Y × Z) :
    aOp (conditionalIdeal P Q f p) *ᵥ ψ =
      bOp (conditionalIdeal R S f p) *ᵥ ψ := by
  unfold conditionalIdeal
  rw [aOp_mul, ← Matrix.mulVec_mulVec, fibSum_mirror ψ P R hP,
    Matrix.mulVec_mulVec, aOp_mul_bOp, ← Matrix.mulVec_mulVec, hQ,
    Matrix.mulVec_mulVec, ← bOp_mul,
    ← (commute_fibSum_right R S hc (f p.1) p.1 p.2).eq]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {H K I Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]
/-- An exact mirror changes a cross-party distance into a same-party distance. -/
theorem xSqNorm_eq_bOp_distance_of_mirror (ψ : H × K → ℂ)
    (P : Matrix H H ℂ) (Q B : Matrix K K ℂ)
    (h : aOp P *ᵥ ψ = bOp Q *ᵥ ψ) :
    xSqNorm ψ P B = snorm ψ (bOp B - bOp Q) ^ 2 := by
  rw [xSqNorm_eq_snorm_sq]
  simp only [snorm, Matrix.sub_mulVec, h, evec_sub]
  rw [norm_sub_rev]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {H K I W : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
/-- Exact mirror transfer followed by cross-party coarse consistency loses
no constant. No same-party coarse-distance contraction is used. -/
theorem mirror_retained_distance_le (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (P : I → Matrix H H ℂ) (Q B : I → Matrix K K ℂ)
    (hP : IsPVM P) (hB : IsPVM B)
    (hmirror : ∀ i, aOp (P i) *ᵥ ψ = bOp (Q i) *ᵥ ψ) (r : I → W) :
    (∑ w, xSqNorm ψ (fibSum P r w) (fibSum B r w)) ≤
      ∑ i, snorm ψ (bOp (B i) - bOp (Q i)) ^ 2 := by
  have h := sum_xSqNorm_fibSum_le hψ hP hB r
  simpa only [xSqNorm_eq_bOp_distance_of_mirror ψ _ _ _ (hmirror _)] using h
end
end MIPRE.Introspection

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PauliAnswer : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype PauliAnswer] {ℓ : ℕ}
/-- The same retention map acts correctly on the entire parsed alphabet,
including every malformed answer constructor. -/
theorem hideNextRetain_parsed (P : CL.CLFun F ι ℓ) (k : ℕ)
    (a : ParsedAnswer (ι → F) A PauliAnswer) :
    hideNextRetain (TypedEstimates.hidingNextLater P k a) =
      TypedEstimates.hidingCoarse P (k + 1) a := by
  cases a <;> rfl
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PauliAnswer : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype PauliAnswer] {ℓ : ℕ}
theorem hideNextRetain_mapped (P : CL.CLFun F ι ℓ) (k : ℕ)
    {K : Type*} [Fintype K] [DecidableEq K]
    (N : POVM (ParsedAnswer (ι → F) A PauliAnswer) K) (z : Option (HideLabel F ι)) :
    fibSum (fun p => ((N.map (TypedEstimates.hidingNextLater P k)).mats p).val)
      hideNextRetain z = ((N.map (TypedEstimates.hidingCoarse P (k + 1))).mats z).val := by
  rw [fibSum, ← POVM.map_mats, POVM.map_map]
  simp only [hideNextRetain_parsed]
end
end MIPRE.Introspection.Honest

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
theorem hidingPrefixOp_transpose (P : CL.CLFun F ι ℓ) (k : ℕ) (y : Option (ι → F)) :
    (hidingPrefixOp P k y)ᵀ = hidingPrefixOp P k y := by
  exact Matrix.diagonal_transpose _
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

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hidingPrefixOp_epr_mirror (P : CL.CLFun F ι ℓ) (k : ℕ) (y : Option (ι → F)) :
    aOp (hidingPrefixOp P k y) *ᵥ registerEPR (ι → F) =
      bOp (hidingPrefixOp P k y) *ᵥ registerEPR (ι → F) := by
  have he := stateVec_epr (hidingPrefixOp P k y)
  rw [hidingPrefixOp_transpose, ← registerEPR_eq_weyl] at he
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

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {V H I Y Z : Type*}
  [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]
theorem conditionalIdeal_aOp (P : I → Matrix V V ℂ) (Q : Y → Matrix V V ℂ)
    (f : Y → I → Z) (p : Y × Z) :
    conditionalIdeal (fun i => (aOp (P i) : Matrix (V × H) _ ℂ))
      (fun y => aOp (Q y)) f p = aOp (conditionalIdeal P Q f p) := by
  rw [conditionalIdeal, fibSum_aOp, ← aOp_mul, conditionalIdeal]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.Honest
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PauliAnswer H K : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype PauliAnswer]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution (P : CL.CLFun F ι ℓ) (k : ℕ)
    (hk : k + 1 < ℓ) (h : P.SupportedOn univ)
    (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (N : POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    (hN : IsPVM (fun a => (N.mats a).val)) {δ : ℝ}
    (hpaired : ∑ p, snorm (registerState (ι → F) ξ)
      (bOp (((N.map (TypedEstimates.hidingNextLater P k)).mats p).val) -
        bOp (conditionalIdeal
          (fun i => (aOp (hideCoarseOp P k h i) : Matrix ((ι → F) × K) _ ℂ))
          (fun y => aOp (hidingPrefixOp P (k + 1) y))
          (TypedEstimates.hidingNextGuarded P k) p)) ^ 2 ≤ δ) :
    (∑ z, xSqNorm (registerState (ι → F) ξ)
      (aOp (hideCoarseOp P (k + 1) h z) : Matrix ((ι → F) × H) _ ℂ)
      (((N.map (TypedEstimates.hidingCoarse P (k + 1))).mats z).val)) ≤ δ := by
  let C := conditionalIdeal (hideCoarseOp P k h) (hidingPrefixOp P (k + 1))
    (TypedEstimates.hidingNextGuarded P k)
  have hc := hidingPrefixOp_commute_coarse P k h (hideLabelCoarse P k)
  have hC : IsPVM C := conditionalIdeal_isPVM _ _ _
    (hideCoarseOp_isPVM P k h) (hidingPrefixOp_isPVM P (k + 1)) hc
  have hseed (p) : aOp (C p) *ᵥ registerEPR (ι → F) = bOp (C p) *ᵥ registerEPR (ι → F) :=
    conditionalIdeal_mirror _ _ _ _ _ _ (hideCoarseOp_epr_mirror P k h)
      (hidingPrefixOp_epr_mirror P (k + 1)) hc p
  have hm (p) :
      aOp (aOp (C p) : Matrix ((ι → F) × H) _ ℂ) *ᵥ registerState (ι → F) ξ =
        bOp (aOp (C p) : Matrix ((ι → F) × K) _ ℂ) *ᵥ registerState (ι → F) ξ :=
    congrArg WithLp.ofLp (mirror_expVec (registerEPR (ι → F)) ξ (C p) (C p)
      (congrArg evec (hseed p)))
  have hret := mirror_retained_distance_le (registerState (ι → F) ξ)
    (registerState_norm ξ hξ)
    (fun p => (aOp (C p) : Matrix ((ι → F) × H) _ ℂ))
    (fun p => (aOp (C p) : Matrix ((ι → F) × K) _ ℂ))
    (fun p => ((N.map (TypedEstimates.hidingNextLater P k)).mats p).val)
    hC.aOp (isPVM_povm_map N hN (TypedEstimates.hidingNextLater P k)) hm hideNextRetain
  have hp : (∑ p, snorm (registerState (ι → F) ξ)
      (bOp (((N.map (TypedEstimates.hidingNextLater P k)).mats p).val) -
        bOp (aOp (C p) : Matrix ((ι → F) × K) _ ℂ)) ^ 2) ≤ δ := by
    simpa only [conditionalIdeal_aOp, C] using hpaired
  have hret' := hret.trans hp
  simpa only [fibSum_aOp, C, hideCoarseOp_conditionalIdeal_step P k hk h,
    hideNextRetain_mapped] using hret'
end MIPRE.Introspection.Honest

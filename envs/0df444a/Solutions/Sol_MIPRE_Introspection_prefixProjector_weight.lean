-- Prove2me | solution 1 for MIPRE.Introspection.prefixProjector_weight
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:21:25.981987+00:00
-- url     : https://prove2.me/submissions/b4597647-fa9b-4faa-940c-4d45c7a03bff

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/PrefixConditioning.lean (solution of MIPRE.Introspection.prefixProjector_weight);
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
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixFactor
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Theorems.Thm_MIPRE_Introspection_CLChecks_truncate_fibre_of_agree
import Theorems.Thm_MIPRE_Introspection_Honest_readout_ambientSplit
import Theorems.Thm_MIPRE_Introspection_bornProb_registerEPR_readout
import Theorems.Thm_MIPRE_Introspection_norm_evec_comp_equiv
import Theorems.Thm_MIPRE_Introspection_readout_isPVM
import Theorems.Thm_MIPRE_Introspection_registerEPR_equiv
import Theorems.Thm_MIPRE_Introspection_registerOp_kronecker
import Theorems.Thm_MIPRE_Introspection_registerOp_mulVec
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_mulVec_kron_expVec
import Theorems.Thm_MIPRE_norm_evec_expVec

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
variable (v : N → ℂ)
/-- **The squared state norm is the quadratic form of `M† M`.** -/
theorem snorm_sq_eq_qform (M : Matrix N N ℂ) : snorm v M ^ 2 = qform v (Mᴴ * M) := by
  rw [snorm, norm_evec_mulVec_sq, qform]
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
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem stateSqNorm_eq_qform (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ M = qform ψ ((aOp (Mᴴ * M) : Matrix (dA × dB) _ ℂ)) := by
  rw [stateSqNorm, stateNorm, norm_stateVec_eq_snorm, snorm_sq_eq_qform, aOp_conjTranspose,
    ← aOp_mul]
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
open Finset Matrix
open scoped Kronecker
variable {V W H K : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- The identity's squared state norm is the squared norm of the state. -/
theorem stateSqNorm_one_eq (ψ : V × W → ℂ) :
    stateSqNorm ψ (1 : Matrix V V ℂ) = ‖evec ψ‖ ^ 2 := by
  simp only [stateSqNorm, stateNorm, stateVec, Matrix.one_kronecker_one,
    Matrix.one_mulVec]
  rfl
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

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem truncate_fibre_congr {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x x' : ι → F)
    (hag : ∀ i ∈ prefixRegister P k y, x i = x' i) :
    (P.truncate k).eval x = y ↔ (P.truncate k).eval x' = y :=
  ⟨truncate_fibre_of_agree hP k y x x' hag,
    truncate_fibre_of_agree hP k y x' x (fun i hi => (hag i hi).symm)⟩
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem truncate_fibre_proj {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    (P.truncate k).eval x = y ↔
      (P.truncate k).eval (CL.proj (prefixRegister P k y) x) = y :=
  truncate_fibre_congr hP k y x _ (fun i hi => by simp [CL.proj_apply, hi])
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem insertRegister_ambientSplit (V : Finset ι) (x : ι → F) :
    insertRegister V (ambientSplit V x).1 = CL.proj V x := by
  ext i
  simp [insertRegister, ambientSplit, CL.proj_apply]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The adaptive ideal prefix has no action on unused coordinates. This is
an exact matrix identity for every claimed prefix, including empty fibres. -/
theorem hidingPrefixOp_factor [Algebra (ZMod 2) F]
    (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ) (y : ι → F) :
    hidingPrefixOp P k (some y) = registerOp (ambientSplit (CLChecks.prefixRegister P k y))
      (prefixProjector P k y ⊗ₖ
        (1 : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ ℂ)) := by
  rw [hidingPrefixOp_some]
  apply readout_ambientSplit
  intro x
  rw [insertRegister_ambientSplit]
  exact CLChecks.truncate_fibre_proj hP k y x
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
theorem readout_const_unit : readout (fun _ : I => ()) () = 1 := by
  ext i j
  simp [readout]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
/-- The squared norm selected by a prefix projector is its actual uniform
seed probability. -/
theorem stateSqNorm_registerEPR_readout (f : I → X) (x : X) :
    stateSqNorm (registerEPR I) (readout f x) = readoutWeight f x := by
  rw [stateSqNorm_eq_qform, (readout_isPVM f).isSelfAdjoint, (readout_isPVM f).idem]
  change bornProb (registerEPR I) (readout f x) 1 = _
  rw [← readout_const_unit, bornProb_registerEPR_readout]
  rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The concrete honest prefix measurement has exactly the actual CL law. -/
theorem hidingPrefixOp_weight [Algebra (ZMod 2) F]
    (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    stateSqNorm (registerEPR (ι → F)) (Honest.hidingPrefixOp P k (some y)) =
      prefixWeight P k y := by
  rw [Honest.hidingPrefixOp_some]
  exact stateSqNorm_registerEPR_readout _ _
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem _root_.solution (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) :
    stateSqNorm (registerEPR (CLChecks.prefixRegister P k y → F)) (prefixProjector P k y) =
      prefixWeight P k y := by
  have hw := hidingPrefixOp_weight P k y
  rw [hidingPrefixOp_factor P hP k y] at hw
  let e := ambientSplit (F := F) (CLChecks.prefixRegister P k y)
  have he : registerEPR (ι → F) =
      expVec (registerEPR (CLChecks.prefixRegister P k y → F))
        (registerEPR (↥((CLChecks.prefixRegister P k y)ᶜ) → F)) ∘ e.prodCongr e := by
    rw [← registerEPR_prod]
    exact (registerEPR_equiv e).symm
  rw [he, stateSqNorm_registerOp, stateSqNorm_expVec_kron, stateSqNorm_one_eq,
    registerEPR_norm, one_pow, mul_one] at hw
  exact hw
end MIPRE.Introspection

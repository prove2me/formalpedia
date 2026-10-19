-- Prove2me | solution 1 for MIPRE.Introspection.prefixResidual_isPVM
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:15:46.002201+00:00
-- url     : https://prove2.me/submissions/e805f331-0fe5-43c9-9274-2486079e48e7

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptivePrefixMeasurement.lean (solution of MIPRE.Introspection.prefixResidual_isPVM);
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
import Theorems.Thm_MIPRE_Introspection_readout_isPVM
import Theorems.Thm_MIPRE_aOp_sum

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
theorem registerParty_kron_one {I J R H : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
    (e : I ≃ J × R) (Q : Matrix J J ℂ) :
    registerOp (registerParty e H) (Q ⊗ₖ (1 : Matrix (R × H) (R × H) ℂ)) =
      (aOp (registerOp e (Q ⊗ₖ (1 : Matrix R R ℂ))) : Matrix (I × H) _ ℂ) := by
  ext ⟨i, h⟩ ⟨j, h'⟩
  simp only [registerOp_apply, registerParty, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.prodAssoc_apply, aOp, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases hr : (e i).2 = (e j).2 <;> by_cases hh : h = h' <;> simp [hr, hh]
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
/-- The normalizer of the reinserted residual family is exactly the ambient
honest prefix projector. -/
theorem prefixResidualOp_one (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) :
    prefixResidualOp (H := H) P k y 1 =
      (aOp (hidingPrefixOp P k (some y)) : Matrix ((ι → F) × H) _ ℂ) := by
  rw [hidingPrefixOp_factor P hP k y]
  exact registerParty_kron_one _ _
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
theorem prefixResidualOp_sum (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    {A : Type*} [Fintype A]
    (M : A → Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    prefixResidualOp P k y (∑ a, M a) = ∑ a, prefixResidualOp P k y (M a) := by
  ext i j
  simp [prefixResidualOp, registerOp_apply, Matrix.kroneckerMap_apply, Matrix.sum_apply,
    Finset.mul_sum]
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
theorem prefixResidualOp_conjTranspose (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    prefixResidualOp P k y Mᴴ = (prefixResidualOp P k y M)ᴴ := by
  unfold prefixResidualOp
  rw [← registerOp_conjTranspose, Matrix.conjTranspose_kronecker]
  have hq : (prefixProjector P k y)ᴴ = prefixProjector P k y :=
    (readout_isPVM _).isSelfAdjoint y
  rw [hq]
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
    (k : ℕ) {A : (ι → F) → Type*} [∀ y, Fintype (A y)]
    (M : (y : ι → F) → A y →
      Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ)
    (hM : ∀ y, IsPVM (M y)) :
    IsPVM (fun p : (y : ι → F) × A y => prefixResidualOp P k p.1 (M p.1 p.2)) where
  isSelfAdjoint p := by rw [← prefixResidualOp_conjTranspose, (hM p.1).isSelfAdjoint]
  idem p := by rw [← prefixResidualOp_mul, (hM p.1).idem]
  sum_eq_one := by
    rw [Fintype.sum_sigma]
    simp_rw [← prefixResidualOp_sum, (hM _).sum_eq_one, prefixResidualOp_one P hP,
      hidingPrefixOp_some]
    rw [← aOp_sum, (readout_isPVM (P.truncate k).eval).sum_eq_one, aOp_one]
end MIPRE.Introspection

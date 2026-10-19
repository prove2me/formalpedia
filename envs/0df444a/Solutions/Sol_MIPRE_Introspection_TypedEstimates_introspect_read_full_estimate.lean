-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.introspect_read_full_estimate
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:50:40.833371+00:00
-- url     : https://prove2.me/submissions/0bb35b20-aaad-4e34-be9c-95db6e472ea3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ProductStageReadTests.lean (solution of MIPRE.Introspection.TypedEstimates.introspect_read_full_estimate);
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
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInduction
import Definitions.Def_MIPRE_Foundations_Introspection_ReadRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageReadTests
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_aux_agreement_estimate
import Theorems.Thm_MIPRE_Weyl_epr_unit

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
/-- The reading edge preserves the introspected question and answer. -/
theorem check_reading (w : Bool) {y z zp : ι → F} {a b : A}
    (h : check L X Z projectPauli D DP (.inr (.introspect, w)) (.inr (.read, w))
      (.pair y a) (.read z zp b) = true) : y = z ∧ a = b := by
  simp [check, fits, directed, CLChecks.reading] at h
  exact @of_decide_eq_true _ (Classical.propDecidable _) h
end
end MIPRE.Introspection.TypedPredicate

namespace MIPRE.Introspection.TypeGraph
section
open QuestionType Finset
set_option linter.unusedSectionVars false
variable {PauliType : Type*} [DecidableEq PauliType] {ℓ : ℕ}
/-- Each Read type is checked against the corresponding introspection. -/
theorem adj_introspect_read (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (w : Bool) : adj (ℓ := ℓ) E X Z (introspect w) (read w) = true := by simp [adj, oriented]
end
end MIPRE.Introspection.TypeGraph

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
theorem _root_.solution (w : Bool) :
    (∑ z, xSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.introspect w, 0)).map introFullPair).mats z).val)
      ((((MB (QuestionType.read w, 0)).map readFullPair).mats z).val)) ≤
      2 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hseed : star (registerEPR (ι → F)) ⬝ᵥ registerEPR (ι → F) = 1 := by
    rw [registerEPR_eq_weyl]
    exact Weyl.epr_unit
  apply aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    (registerState (ι → F) ξ) (expVec_unit hseed hξ) MA MB hfail .introspect .read w w
    (TypeGraph.adj_introspect_read E X Z w)
  intro a b hab
  have hf := TypedPredicate.check_formats L X Z projectPauli D (fun p s => DP p s 0 0) hab
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i y a z zp b
  have he := TypedPredicate.check_reading L X Z projectPauli D (fun p s => DP p s 0 0) w hab
  exact congrArg some (Prod.ext he.1 he.2)
end MIPRE.Introspection.TypedEstimates

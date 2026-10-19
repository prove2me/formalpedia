-- Prove2me | solution 1 for MIPRE.Introspection.Honest.hideRegister_entry_supported
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:04:17.535174+00:00
-- url     : https://prove2.me/submissions/951abfb0-322e-4f07-9c44-eb66f7cff76c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestLabelSupport.lean (solution of MIPRE.Introspection.Honest.hideRegister_entry_supported);
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
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_SampledGame
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
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem dualReadout_first_supported (P : CL.CLFun F ι ℓ) (x : ι → F) :
    CL.proj (P.factorOfPrefix 0 0) (CLChecks.dualReadout P 0 0 x) =
      CLChecks.dualReadout P 0 0 x := by
  cases P with
  | zero => simp [CLChecks.dualReadout]
  | cons S L next =>
    simp only [CL.CLFun.factorOfPrefix_cons_zero, CLChecks.dualReadout]
    ext i
    by_cases hi : i ∈ S <;> simp [CL.proj_apply, coordinateInsert, hi]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem proj_coordinateInsert_of_subset {S V : Finset ι} (h : S ⊆ V)
    (x : Fin (Fintype.card S) → F) : CL.proj V (coordinateInsert S x) = coordinateInsert S x := by
  funext i
  by_cases hi : i ∈ S
  · simp [CL.proj_apply, coordinateInsert, hi, h hi]
  · simp [CL.proj_apply, coordinateInsert, hi]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
/-- All three stopping-Hide vectors are supported on the active register. -/
theorem stopHideAnswer_supported {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) (x : V → F) :
    CL.proj V (stopHideAnswer P V x).1 = (stopHideAnswer P V x).1 ∧
    CL.proj V (stopHideAnswer P V x).2.1 = (stopHideAnswer P V x).2.1 ∧
    CL.proj V (stopHideAnswer P V x).2.2 = (stopHideAnswer P V x).2.2 := by
  have hS : P.factorOfPrefix 0 0 ⊆ V := by
    cases P with
    | zero => simp [CL.CLFun.factorOfPrefix]
    | cons S L next => exact h.1
  refine ⟨by simp [stopHideAnswer, firstHideAnswer], ?_, ?_⟩
  · exact support_mono hS (dualReadout_first_supported P (insertRegister V x))
  · change CL.proj V (CL.proj (P.factorOfPrefix 0 0)ᶜ (insertRegister V x)) =
      CL.proj (P.factorOfPrefix 0 0)ᶜ (insertRegister V x)
    funext i
    by_cases hi : i ∈ V <;> simp [CL.proj_apply, insertRegister, hi]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
/-- A nonzero stopping-Hide entry has no reported coordinates outside its register. -/
theorem stopHide_entry_supported {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) (a : HideLabel F ι) (x x' : V → F)
    (ha : stopHide P V a x x' ≠ 0) :
    CL.proj V a.1 = a.1 ∧ CL.proj V a.2.1 = a.2.1 ∧ CL.proj V a.2.2 = a.2.2 := by
  simp only [stopHide, synOf, Matrix.sum_apply] at ha
  obtain ⟨z, hz, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  rw [← (Finset.mem_filter.mp hz).2]
  exact stopHideAnswer_supported P V h z
end
end MIPRE.Introspection.Honest

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.Honest
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem _root_.solution {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (V : Finset ι) (h : P.SupportedOn V) (a : HideLabel F ι) (x x' : V → F)
    (ha : hideRegister P k V h a x x' ≠ 0) :
    CL.proj V a.1 = a.1 ∧ CL.proj V a.2.1 = a.2.1 ∧ CL.proj V a.2.2 = a.2.2 := by
  induction P generalizing V a k with
  | zero =>
      cases k <;> exact stopHide_entry_supported .zero V h a x x' ha
  | cons S L next ih =>
      cases k with
      | zero => exact stopHide_entry_supported _ V h a x x' ha
      | succ k =>
          simp only [hideRegister, registerOp_apply, Matrix.sum_apply] at ha
          obtain ⟨q, hq, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
          have hj := (Finset.mem_filter.mp hq).2
          change localRead L q.1 (coordinateSplit S V h.1 x).1
              (coordinateSplit S V h.1 x').1 *
            hideRegister (next (coordinateInsert S q.1.1)) k (V \ S) (h.2 _)
              q.2 (coordinateSplit S V h.1 x).2 (coordinateSplit S V h.1 x').2 ≠ 0 at hterm
          have hr := ih (coordinateInsert S q.1.1) k (V \ S) (h.2 _) q.2
            (coordinateSplit S V h.1 x).2 (coordinateSplit S V h.1 x').2
            (mul_ne_zero_iff.mp hterm).2
          rw [← hj]
          refine ⟨?_, ?_, support_mono sdiff_subset hr.2.2⟩
          · change CL.proj V (coordinateInsert S q.1.1 + q.2.1) = _
            rw [map_add, proj_coordinateInsert_of_subset h.1, support_mono sdiff_subset hr.1]
            rfl
          · change CL.proj V (coordinateInsert S q.1.2 + q.2.2.1) = _
            rw [map_add, proj_coordinateInsert_of_subset h.1, support_mono sdiff_subset hr.2.1]
            rfl
end MIPRE.Introspection.Honest

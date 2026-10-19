-- Prove2me | solution 1 for MIPRE.Introspection.Honest.hidingNext_stop_join
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:54:54.906729+00:00
-- url     : https://prove2.me/submissions/fe39fbeb-f8f1-48f3-ae1b-a0b2bee851fe

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestHidingChecks.lean (solution of MIPRE.Introspection.Honest.hidingNext_stop_join);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.Honest
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem _root_.solution {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (h : (CL.CLFun.cons S L next).SupportedOn V)
    (z : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
    (x : ↥(V \ S) → F) :
    CLChecks.hidingNext (.cons S L next) 0 (stopLabel S V (z.2, x))
      (joinHide S (z, stopHideAnswer (next (coordinateInsert S z.1)) (V \ S) x)) := by
  let Q := next (coordinateInsert S z.1)
  let t := insertRegister (V \ S) x
  let d := CLChecks.dualReadout Q 0 0 t
  let T := Q.factorOfPrefix 0 0
  have hQ : Q.SupportedOn (V \ S) := h.2 _
  have hT : T ⊆ V \ S := factorOfPrefix_subset hQ 0 0
  have hd : CL.proj (V \ S) d = d :=
    (stopHideAnswer_supported Q (V \ S) hQ x).2.1
  have hdT : CL.proj T d = d := dualReadout_first_supported Q t
  have hroot := proj_local_add (V := V) z.1 (0 : ι → F) (map_zero _)
  simp only [add_zero] at hroot
  have hp : CLChecks.prefixRegister Q 1 0 = T := by
    change CLChecks.prefixRegister Q 1 0 = Q.factorOfPrefix 0 0
    cases Q <;> simp [CLChecks.prefixRegister]
  have hcomp : (S ∪ T)ᶜ ⊆ Tᶜ := by
    intro i hi
    exact mem_compl.mpr fun ht => (mem_compl.mp hi) (mem_union_right S ht)
  change CLChecks.hidingNext (.cons S L next) 0
    (0, coordinateInsert S z.2, t)
    (coordinateInsert S z.1 + 0, coordinateInsert S z.2 + d, CL.proj Tᶜ t)
  simp only [add_zero, CLChecks.hidingNext, CL.CLFun.outputPrefix_zero]
  refine ⟨True.intro, ?_, ?_, ?_⟩
  · simp only [CLChecks.prefixRegister, hroot.1, hroot.2, union_empty]
    rw [(proj_local_add z.2 d hd).1, proj_coordinateInsert_of_subset (Subset.rfl)]
  · simp only [CLChecks.prefixRegister, hroot.1, hroot.2]
    change CL.proj (S ∪ CLChecks.prefixRegister Q 1 0)ᶜ t =
      CL.proj (S ∪ CLChecks.prefixRegister Q 1 0)ᶜ (CL.proj Tᶜ t)
    rw [hp, CL.proj_proj_of_subset hcomp]
  · simp only [CL.CLFun.factorOfPrefix_cons_succ, CL.CLFun.outputPrefix_cons,
      CLChecks.dualReadout, hroot.1, hroot.2, CL.CLFun.outputPrefix_zero, add_zero]
    change CL.proj T (coordinateInsert S z.2 + d) = d
    rw [proj_tail_local_add hT z.2 d, hdT]
end MIPRE.Introspection.Honest

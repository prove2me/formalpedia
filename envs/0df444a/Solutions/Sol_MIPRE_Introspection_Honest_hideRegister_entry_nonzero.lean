-- Prove2me | solution 1 for MIPRE.Introspection.Honest.hideRegister_entry_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:45:41.188351+00:00
-- url     : https://prove2.me/submissions/8e86dfbd-153d-4654-a60a-34a7708d84f1

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestHiding.lean (solution of MIPRE.Introspection.Honest.hideRegister_entry_nonzero);
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
import Theorems.Thm_MIPRE_Introspection_readout_eq_synOf

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
variable [Field F]
theorem coordinateInsert_restrict (U : Finset ι) (v : ι → F) :
    coordinateInsert U (coordinateRestrict U v) = CL.proj U v := by
  funext i
  by_cases hi : i ∈ U
  · simp only [coordinateInsert, coordinateRestrict, LinearMap.coe_mk, AddHom.coe_mk,
      dif_pos hi, Equiv.symm_apply_apply, CL.proj_apply, if_pos hi]
  · simp only [coordinateInsert, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hi,
      CL.proj_apply, if_neg hi]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
variable [Field F]
/-- Restricting the ambient CL linear map commutes with passing to register coordinates. -/
theorem coordinateLinear_restrict {U : Finset ι} (L : CL.RegLinear F U) (v : ι → F) :
    coordinateLinear L (coordinateRestrict U v) = coordinateRestrict U (L v) := by
  simp only [coordinateLinear, LinearMap.comp_apply, coordinateInsert_restrict,
    CL.RegLinear.toLinearMap_apply, CL.RegLinear.apply_proj]
end
end MIPRE.Introspection

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem restrict_insertRegister (S V : Finset ι) (h : S ⊆ V) (x : V → F) :
    coordinateRestrict S (insertRegister V x) = (coordinateSplit S V h x).1 := by
  funext i
  simp [coordinateRestrict, insertRegister, coordinateSplit,
    h ((Fintype.equivFin S).symm i).property]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem linear_insertRegister {S V : Finset ι} (h : S ⊆ V)
    (L : CL.RegLinear F S) (x : V → F) :
    L (insertRegister V x) =
      coordinateInsert S (coordinateLinear L (coordinateSplit S V h x).1) := by
  rw [← restrict_insertRegister S V h, coordinateLinear_restrict,
    coordinateInsert_restrict, CL.RegLinear.proj_apply]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem tail_insertRegister (S V : Finset ι) (h : S ⊆ V) (x : V → F) :
    CL.proj Sᶜ (insertRegister V x) =
      insertRegister (V \ S) (coordinateSplit S V h x).2 := by
  funext i
  by_cases hiS : i ∈ S <;> by_cases hiV : i ∈ V <;>
    simp [CL.proj_apply, insertRegister, coordinateSplit, hiS, hiV]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem localRead_entry_nonzero {S : Finset ι} (L : CL.RegLinear F S)
    (a : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
    (x x' : Fin (Fintype.card S) → F) (h : localRead L a x x' ≠ 0) :
    coordinateLinear L x = a.1 := by
  by_contra hn
  apply h
  rw [localRead, ← readout_eq_synOf, readout, Matrix.diagonal_mul]
  simp [hn]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem stopHide_entry_nonzero {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (V : Finset ι)
    (a : HideLabel F ι) (x x' : V → F) (ha : stopHide P V a x x' ≠ 0) : a.1 = 0 := by
  simp only [stopHide, synOf, Matrix.sum_apply] at ha
  obtain ⟨z, hz, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  exact (congrArg Prod.fst (Finset.mem_filter.mp hz).2).symm
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
    (P.truncate k).eval (insertRegister V x) = a.1 := by
  induction P generalizing V a k with
  | zero =>
      cases k with
      | zero => exact (stopHide_entry_nonzero .zero V a x x' ha).symm
      | succ k =>
          rw [CL.CLFun.eval_truncate_zero]
          exact (stopHide_entry_nonzero .zero V a x x' ha).symm
  | cons S L next ih =>
      cases k with
      | zero => exact (stopHide_entry_nonzero _ V a x x' ha).symm
      | succ k =>
          simp only [hideRegister, registerOp_apply, Matrix.sum_apply] at ha
          obtain ⟨q, hq, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
          have hj := (Finset.mem_filter.mp hq).2
          change localRead L q.1 (coordinateSplit S V h.1 x).1
              (coordinateSplit S V h.1 x').1 *
            hideRegister (next (coordinateInsert S q.1.1)) k (V \ S) (h.2 _)
              q.2 (coordinateSplit S V h.1 x).2 (coordinateSplit S V h.1 x').2 ≠ 0 at hterm
          have hl := localRead_entry_nonzero L q.1 _ _ (mul_ne_zero_iff.mp hterm).1
          have hr := ih (coordinateInsert S q.1.1) k (V \ S) (h.2 _) q.2
            (coordinateSplit S V h.1 x).2 (coordinateSplit S V h.1 x').2
            (mul_ne_zero_iff.mp hterm).2
          rw [CL.CLFun.truncate_succ_cons, CL.CLFun.eval_cons,
            linear_insertRegister h.1 L x, hl, tail_insertRegister S V h.1 x, hr]
          exact congrArg Prod.fst hj
end MIPRE.Introspection.Honest

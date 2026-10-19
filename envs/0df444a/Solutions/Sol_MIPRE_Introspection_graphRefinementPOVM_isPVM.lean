-- Prove2me | solution 1 for MIPRE.Introspection.graphRefinementPOVM_isPVM
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:46:35.84731+00:00
-- url     : https://prove2.me/submissions/28616738-d205-407d-b510-2f5f9f12e95c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AnswerRefinement.lean (solution of MIPRE.Introspection.graphRefinementPOVM_isPVM);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
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
import Definitions.Def_MIPRE_Foundations_Introspection_AnswerRefinement

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
theorem graphRefinement_sum_coordinate (M : A → Matrix D D ℂ) (c : A → C) (a : A) :
    (∑ z, graphRefinement M c (z, a)) = M a := by simp [graphRefinement]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
theorem graphRefinement_isPVM (M : A → Matrix D D ℂ) (c : A → C) (hM : IsPVM M) :
    IsPVM (graphRefinement M c) where
  isSelfAdjoint p := by
    by_cases hp : p.1 = c p.2 <;> simp [graphRefinement, hp, hM.isSelfAdjoint]
  idem p := by
    by_cases hp : p.1 = c p.2 <;> simp [graphRefinement, hp, hM.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simpa only [graphRefinement_sum_coordinate] using hM.sum_eq_one
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
theorem graphRefinement_eq_fibSum (M : A → Matrix D D ℂ) (c : A → C) (p : C × A) :
    graphRefinement M c p = fibSum M (fun a => (c a, a)) p := by
  rcases p with ⟨z, a⟩
  simp only [fibSum, Finset.sum_filter, Prod.mk.injEq]
  rw [Finset.sum_eq_single a]
  · simp [graphRefinement, eq_comm]
  · intro b _ hba
    simp [hba]
  · simp
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
theorem graphRefinementPOVM_mats (M : POVM A D) (c : A → C) (p : C × A) :
    ((graphRefinementPOVM M c).mats p).val =
      graphRefinement (fun a => (M.mats a).val) c p := by
  rw [graphRefinement_eq_fibSum]
  exact POVM.map_mats _ _ _
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
theorem _root_.solution (M : POVM A D) (c : A → C)
    (hM : IsPVM (fun a => (M.mats a).val)) :
    IsPVM (fun p => ((graphRefinementPOVM M c).mats p).val) := by
  simpa only [graphRefinementPOVM_mats] using graphRefinement_isPVM _ c hM
end MIPRE.Introspection

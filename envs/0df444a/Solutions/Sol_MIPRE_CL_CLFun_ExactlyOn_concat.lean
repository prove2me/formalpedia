-- Prove2me | solution 1 for MIPRE.CL.CLFun.ExactlyOn.concat
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:38:50.214409+00:00
-- url     : https://prove2.me/submissions/83a7422a-c65a-4a77-b719-d9630f2432a3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Closure.lean (solution of MIPRE.CL.CLFun.ExactlyOn.concat);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun.ExactlyOn
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {k ℓ : ℕ}
theorem _root_.solution {L : CLFun F ι k} {R : (ι → F) → CLFun F ι ℓ} {U W : Finset ι}
    (hL : L.ExactlyOn U) (hR : ∀ u, (R u).ExactlyOn W) (hUW : Disjoint U W) :
    (L.concat R).ExactlyOn (U ∪ W) := by
  induction L generalizing R U with
  | zero =>
    have hU : U = ∅ := hL
    rw [concat_zero, hU, Finset.empty_union]
    exact hR 0
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hL
    refine ⟨hS.trans Finset.subset_union_left, fun v => ?_⟩
    rw [Finset.union_sdiff_distrib,
      Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_of_subset_left hS hUW).symm]
    exact ih v (hnext v) (fun w => hR _) (Finset.disjoint_of_subset_left Finset.sdiff_subset hUW)
end MIPRE.CL.CLFun.ExactlyOn

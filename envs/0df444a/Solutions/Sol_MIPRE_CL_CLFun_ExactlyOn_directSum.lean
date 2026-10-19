-- Prove2me | solution 1 for MIPRE.CL.CLFun.ExactlyOn.directSum
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:38:50.985593+00:00
-- url     : https://prove2.me/submissions/b27c7cde-1bda-494f-a020-2f196a764c42

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Closure.lean (solution of MIPRE.CL.CLFun.ExactlyOn.directSum);
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
theorem _root_.solution {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.ExactlyOn T)
    (hQ : Q.ExactlyOn T') (hTT' : Disjoint T T') : (P.directSum Q).ExactlyOn (T ∪ T') := by
  induction P generalizing T T' with
  | zero =>
    rw [Q.eq_zero] at hQ ⊢
    have hT : T = ∅ := hP
    have hT' : T' = ∅ := hQ
    show T ∪ T' = ∅
    rw [hT, hT', Finset.empty_union]
  | cons S L₁ next ih =>
    cases Q with
    | cons S' L₁' next' =>
      obtain ⟨hS, hnext⟩ := hP
      obtain ⟨hS', hnext'⟩ := hQ
      refine ⟨Finset.union_subset_union hS hS', fun v => ?_⟩
      show ((next (proj S v)).directSum (next' (proj S' v))).ExactlyOn ((T ∪ T') \ (S ∪ S'))
      rw [union_sdiff_union hS hS' hTT']
      exact ih _ (hnext _) (hnext' _) (Finset.disjoint_of_subset_left Finset.sdiff_subset
        (Finset.disjoint_of_subset_right Finset.sdiff_subset hTT'))
end MIPRE.CL.CLFun.ExactlyOn

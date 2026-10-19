-- Prove2me | solution 1 for MIPRE.CL.CLFun.SupportedOn.mapAt_apply_proj
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:20:44.039173+00:00
-- url     : https://prove2.me/submissions/ca482c8b-127e-4e61-9c94-0f2ab6340b90

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Basic.lean (solution of MIPRE.CL.CLFun.SupportedOn.mapAt_apply_proj);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun.SupportedOn
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
theorem _root_.solution {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (hTU : T ⊆ U) (k : ℕ) (x y : ι → F) : P.mapAt k x (proj U y) = P.mapAt k x y := by
  induction P generalizing T U k x y with
  | zero => simp
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    cases k with
    | zero =>
      rw [mapAt_cons_zero, RegLinear.toLinearMap_apply, RegLinear.toLinearMap_apply]
      exact L₁.apply_proj_of_subset (hS.trans hTU) y
    | succ k =>
      rw [mapAt_cons_succ]
      exact ih _ (hnext _) (Finset.sdiff_subset.trans hTU) k _ y
end MIPRE.CL.CLFun.SupportedOn

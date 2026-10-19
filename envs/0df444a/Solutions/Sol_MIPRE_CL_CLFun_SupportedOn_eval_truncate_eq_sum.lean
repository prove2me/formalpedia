-- Prove2me | solution 1 for MIPRE.CL.CLFun.SupportedOn.eval_truncate_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:21:14.108212+00:00
-- url     : https://prove2.me/submissions/392ebc82-f168-4c23-bc7f-91f46ca6bd95

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Basic.lean (solution of MIPRE.CL.CLFun.SupportedOn.eval_truncate_eq_sum);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Theorems.Thm_MIPRE_CL_CLFun_SupportedOn_mapAt_apply_proj

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun.SupportedOn
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
theorem _root_.solution {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (k : ℕ) (x : ι → F) : (P.truncate k).eval x = ∑ i ∈ Finset.range k, P.mapAt i x x := by
  induction k generalizing ℓ P T x with
  | zero => simp
  | succ k ih =>
    cases P with
    | zero => simp
    | cons S L₁ next =>
      obtain ⟨hS, hnext⟩ := hP
      have hsub : T \ S ⊆ Sᶜ := fun i hi => by
        simp only [Finset.mem_sdiff] at hi
        simpa using hi.2
      rw [truncate_succ_cons, eval_cons, ih (hnext (L₁ x)) (proj Sᶜ x), Finset.sum_range_succ',
        mapAt_cons_zero, RegLinear.toLinearMap_apply, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mapAt_cons_succ, (hnext (L₁ x)).mapAt_apply_proj hsub i (proj Sᶜ x) x]
end MIPRE.CL.CLFun.SupportedOn

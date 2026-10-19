-- Prove2me | solution 1 for MIPRE.CL.CLFun.mapOfPrefix_reindex
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:40:01.103984+00:00
-- url     : https://prove2.me/submissions/0705c98d-fb18-4830-b8cb-4f945fc07976

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Downsize.lean (solution of MIPRE.CL.CLFun.mapOfPrefix_reindex);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Downsize

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable [DecidableEq ι'] [Fintype ι']
variable {ℓ : ℕ}
theorem map_compl (e : ι ≃ ι') (S : Finset ι) : (S.map e.toEmbedding)ᶜ = Sᶜ.map e.toEmbedding := by
  ext i; simp [Finset.mem_map_equiv]
end
end MIPRE.CL.CLFun

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable [DecidableEq ι'] [Fintype ι']
variable {ℓ : ℕ}
theorem _root_.solution (e : ι ≃ ι') (P : CLFun F ι ℓ) (k : ℕ) (u : ι → F) :
    (P.reindex e).mapOfPrefix k (reindexEquiv e u) =
      (reindexEquiv e).toLinearMap ∘ₗ P.mapOfPrefix k u ∘ₗ (reindexEquiv e).symm.toLinearMap := by
  induction P generalizing k u with
  | zero => ext y; simp
  | cons S L₁ next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [reindex_cons, mapOfPrefix_cons_succ, mapOfPrefix_cons_succ, map_compl,
        ← reindexEquiv_proj, ← reindexEquiv_proj, LinearEquiv.symm_apply_apply, ih]
end MIPRE.CL.CLFun

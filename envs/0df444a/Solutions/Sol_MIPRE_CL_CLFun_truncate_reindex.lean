-- Prove2me | solution 1 for MIPRE.CL.CLFun.truncate_reindex
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:39:53.498815+00:00
-- url     : https://prove2.me/submissions/fa9881c9-47e1-493e-a00b-c5552e7b48b6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Downsize.lean (solution of MIPRE.CL.CLFun.truncate_reindex);
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
namespace MIPRE.CL
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [DecidableEq ι']
theorem map_sdiff' (e : ι ≃ ι') (S T : Finset ι) :
    T.map e.toEmbedding \ S.map e.toEmbedding = (T \ S).map e.toEmbedding := by
  ext i; simp [Finset.mem_map_equiv]
end
end MIPRE.CL

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [DecidableEq ι']
variable {ℓ : ℕ}
theorem lift_reindex (e : ι ≃ ι') (T : Finset ι) (P : CLFun F ι ℓ) :
    (P.lift T).reindex e = (P.reindex e).lift (T.map e.toEmbedding) := by
  induction P generalizing T with
  | zero => simp [lift]
  | cons S L₁ next ih =>
    simp only [lift, reindex_cons]
    congr 1
    funext v
    rw [ih, map_sdiff']
end
end MIPRE.CL.CLFun

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [DecidableEq ι']
variable {ℓ : ℕ}
theorem _root_.solution (e : ι ≃ ι') (k : ℕ) (P : CLFun F ι ℓ) :
    (P.reindex e).truncate k = (P.truncate k).reindex e := by
  induction k generalizing ℓ P with
  | zero => simp
  | succ k ih =>
    cases P with
    | zero =>
      rw [reindex_zero, truncate_succ_zero, truncate_succ_zero, lift_reindex, ← ih, reindex_zero,
        Finset.map_empty]
    | cons S L₁ next =>
      rw [reindex_cons, truncate_succ_cons, truncate_succ_cons, reindex_cons]
      congr 1
      funext v
      exact ih _
end MIPRE.CL.CLFun

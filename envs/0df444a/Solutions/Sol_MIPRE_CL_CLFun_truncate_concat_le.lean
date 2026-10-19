-- Prove2me | solution 1 for MIPRE.CL.CLFun.truncate_concat_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:23.411205+00:00
-- url     : https://prove2.me/submissions/78021656-9bbd-45f2-956d-5b6ad97f410d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingQueries.lean (solution of MIPRE.CL.CLFun.truncate_concat_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun
open Finset Classical
variable {F ι : Type*} [Semiring F] [DecidableEq ι] {k ℓ : ℕ}
theorem _root_.solution (L : CLFun F ι k) (R : (ι → F) → CLFun F ι ℓ)
    (j : ℕ) (hj : j ≤ k) : (L.concat R).truncate j = L.truncate j := by
  induction L generalizing R j with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp
  | cons S L next ih =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [concat_cons, truncate_succ_cons]
      congr 1
      funext x
      exact ih x _ j (by omega)
end MIPRE.CL.CLFun

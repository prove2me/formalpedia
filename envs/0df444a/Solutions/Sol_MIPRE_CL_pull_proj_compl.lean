-- Prove2me | solution 1 for MIPRE.CL.pull_proj_compl
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:40:02.009331+00:00
-- url     : https://prove2.me/submissions/85ef6ea6-d81c-4296-9bc7-c120d753cd7e

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Embedding.lean (solution of MIPRE.CL.pull_proj_compl);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Embedding

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL
open Classical
set_option linter.unusedSectionVars false
variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]
theorem _root_.solution [Fintype ι] [Fintype κ] (e : ι ↪ κ) (S : Finset ι)
    (x : κ → F) : pull e (proj (S.map e)ᶜ x) = proj Sᶜ (pull e x) := by
  funext i
  simp [pull]
end MIPRE.CL

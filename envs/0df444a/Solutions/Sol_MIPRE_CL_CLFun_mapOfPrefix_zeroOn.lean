-- Prove2me | solution 1 for MIPRE.CL.CLFun.mapOfPrefix_zeroOn
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:38:51.700472+00:00
-- url     : https://prove2.me/submissions/27cc5743-aacc-45a5-bdec-421161b9ad9d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Detyping.lean (solution of MIPRE.CL.CLFun.mapOfPrefix_zeroOn);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Semiring F] [DecidableEq ι]
theorem _root_.solution [Fintype ι] (S : Finset ι) (ℓ j : ℕ) (x : ι → F) :
    (zeroOn (F := F) S ℓ).mapOfPrefix j x = 0 := by
  induction ℓ generalizing S j x with
  | zero => rfl
  | succ ℓ ih =>
    cases j with
    | zero => rfl
    | succ j => simp [zeroOn, ih]
end MIPRE.CL.CLFun

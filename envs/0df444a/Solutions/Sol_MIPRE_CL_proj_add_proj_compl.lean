-- Prove2me | solution 1 for MIPRE.CL.proj_add_proj_compl
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:42:14.286881+00:00
-- url     : https://prove2.me/submissions/2d83a860-82a1-4bed-93a3-ab89616de37f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Register.lean (solution of MIPRE.CL.proj_add_proj_compl);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
theorem _root_.solution [Fintype ι] (S : Finset ι) (x : ι → F) :
    proj S x + proj Sᶜ x = x := by
  ext i; by_cases h : i ∈ S <;> simp [h]
end MIPRE.CL

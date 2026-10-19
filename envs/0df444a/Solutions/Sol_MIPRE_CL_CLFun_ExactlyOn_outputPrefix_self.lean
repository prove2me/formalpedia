-- Prove2me | solution 1 for MIPRE.CL.CLFun.ExactlyOn.outputPrefix_self
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:26:06.372343+00:00
-- url     : https://prove2.me/submissions/46df2ad8-f345-45fc-aea6-d68ae402195e

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SamplingPrefix.lean (solution of MIPRE.CL.CLFun.ExactlyOn.outputPrefix_self);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Theorems.Thm_MIPRE_CL_proj_add_proj_compl

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun.ExactlyOn
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem _root_.solution {P : CLFun F ι ℓ} {T : Finset ι}
    (hP : P.ExactlyOn T) (y : ι → F) : P.outputPrefix ℓ (proj T y) = proj T y := by
  induction P generalizing T y with
  | zero =>
    have hT : T = ∅ := hP
    simp [hT, outputPrefix]
  | cons S L next ih =>
    obtain ⟨hS, hnext⟩ := hP
    rw [outputPrefix_cons, proj_proj_of_subset hS]
    have hp : proj Sᶜ (proj T y) = proj (T \ S) y := by
      rw [proj_proj, inter_comm, ← sdiff_eq_inter_compl]
    rw [hp, ih _ (hnext _) y]
    have hp' : proj (T \ S) y = proj Sᶜ (proj T y) := hp.symm
    rw [hp', ← proj_proj_of_subset hS y, proj_add_proj_compl]
end MIPRE.CL.CLFun.ExactlyOn

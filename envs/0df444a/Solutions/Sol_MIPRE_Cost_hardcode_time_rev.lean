-- Prove2me | solution 1 for MIPRE.Cost.hardcode_time_rev
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:35:43.551872+00:00
-- url     : https://prove2.me/submissions/102c236d-9b2c-44db-aa27-3e1284ad3aa7

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Toolkit.lean (solution of MIPRE.Cost.hardcode_time_rev);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Eval_of_append_of_wellScoped

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost
open Polynomial
/-- The run of the pairing prefix of `hardcode`. -/
theorem hardcode_prefix_eval (d x : Data) :
    Eval [x] (.cons (.const d) (.var 0)) (.cons d x) (d.size + (x.size + 1) + 1) :=
  .cons (.const _ _) (Eval.var_of_get (by simp))
end MIPRE.Cost

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution {p : Prog} (hp : p.WellScoped 1) {d x r : Data} {t : ℕ}
    (h : (hardcode p d).Runs x r t) : ∃ t' ≤ t, p.Runs (.cons d x) r t' := by
  change Eval [x] (.let_ (.cons (.const d) (.var 0)) p) r t at h
  cases h with
  | let_ h₁ h₂ =>
    obtain ⟨rfl, -⟩ := h₁.deterministic (hardcode_prefix_eval d x)
    exact ⟨_, by omega,
      Eval.of_append_of_wellScoped (env := [.cons d x]) (extra := [x]) h₂ hp⟩

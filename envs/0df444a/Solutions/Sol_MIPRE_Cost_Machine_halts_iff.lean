-- Prove2me | solution 1 for MIPRE.Cost.Machine.halts_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:37:17.253778+00:00
-- url     : https://prove2.me/submissions/1e06a940-4a9e-421c-86a6-f665a3a1ea8f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Machine.lean (solution of MIPRE.Cost.Machine.halts_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Theorems.Thm_MIPRE_Cost_Machine_eval_of_steps
import Theorems.Thm_MIPRE_Cost_Machine_eval_steps

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
theorem solution (p : Prog) (x r : Data) :
    (∃ t, p.Runs x r t) ↔ ∃ N e, step^[N] ⟨.ev p, [x], []⟩ = ⟨.ret r, e, []⟩ := by
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨N, e, hs⟩ := eval_steps h []
    exact ⟨N, e, hs.1⟩
  · rintro ⟨N, e, h⟩
    obtain ⟨r', t, M, e', N', hN, hev, hs⟩ := eval_of_steps N p [x] [] r e h
    -- the final configuration is fixed, so `r' = r`
    have hfix : ∀ n, step^[n] (⟨.ret r', e', []⟩ : Cfg) = ⟨.ret r', e', []⟩ := fun n =>
      Function.iterate_fixed rfl n
    rw [hN, Nat.add_comm, Function.iterate_add_apply, hs.1, hfix] at h
    obtain rfl := Ctrl.ret.inj (Cfg.mk.inj h).1
    exact ⟨t, hev⟩

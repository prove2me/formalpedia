-- Prove2me | solution 1 for Groundwork.PolyT.elim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:45:32.741051+00:00
-- url     : https://prove2.me/submissions/12647064-b3d6-4158-91c4-d83c6866c886

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Enc
import Definitions.Def_ToTuring_TM_Ops
import Definitions.Def_ToTuring_Bound
import Mathlib.Tactic.FunProp
import Definitions.Def_ToTuring_PolyT
import Theorems.Thm_Groundwork_PB_mono_bound


set_option autoImplicit false
section
section
open Groundwork
open TM
namespace Groundwork
namespace PolyT
theorem _root_.solution {α β : Type} [Enc α] [Enc β] {f : α → β} (h : PolyT f) : ∃ (P : Fr) (t : ℕ → ℕ), PB t ∧ Monotone t ∧
    (∀ (x : α) (M A B N : List Sym), P.Within (st (wd x ++ M) A B N) (t (len x)) (st (wd (f x) ++ M) A B N)) ∧
    ∀ x, len (f x) ≤ t (len x) := by
  obtain ⟨P, c, h1, h2⟩ := h
  exact ⟨P, fun n => c * (n + 1) ^ c, (PB.mono_bound c).1, (PB.mono_bound c).2, h1, h2⟩
end PolyT
end Groundwork

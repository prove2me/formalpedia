-- Prove2me | solution 1 for Groundwork.PolyT.of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:45:54.903029+00:00
-- url     : https://prove2.me/submissions/364d9fab-24bc-4866-b912-a31e07869fee

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Enc
import Definitions.Def_ToTuring_TM_Ops
import Definitions.Def_ToTuring_Bound
import Mathlib.Tactic.FunProp
import Definitions.Def_ToTuring_PolyT
import Theorems.Thm_Groundwork_PB_bound_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Groundwork
open TM
namespace Groundwork
namespace PolyT
theorem _root_.solution {α β : Type} [Enc α] [Enc β] {f : α → β} (P : Fr) {t s : ℕ → ℕ} (ht : PB t) (hs : PB s)
    (h : ∀ (x : α) (M A B N : List Sym), P.Within (st (wd x ++ M) A B N) (t (len x)) (st (wd (f x) ++ M) A B N))
    (hl : ∀ x, len (f x) ≤ s (len x)) : PolyT f := by
  obtain ⟨c, hc⟩ := ht
  obtain ⟨c', hc'⟩ := hs
  refine ⟨P, c + c', fun x M A B N => ?_, fun x => ?_⟩
  · obtain ⟨n, hn, hr⟩ := h x M A B N
    exact ⟨n, (hn.trans (hc _)).trans (PB.bound_le (Nat.le_add_right _ _) (Nat.le_add_right _ _)), hr⟩
  · exact ((hl x).trans (hc' _)).trans (PB.bound_le (Nat.le_add_left _ _) (Nat.le_add_left _ _))
end PolyT
end Groundwork

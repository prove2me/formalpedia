-- Prove2me | solution 1 for Groundwork.PolyT.len_bound_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:35:34.288803+00:00
-- url     : https://prove2.me/submissions/ef57d522-2a2e-4244-a88d-0cf8b723b898

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_ToTuring_Lib_List1
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_len_le_of_mem
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution {f : α → β → γ} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    ∃ b, PB b ∧ ∀ x, ∀ e ∈ l x, len (f x e) ≤ b (len x) := by
  obtain ⟨t, ht, hm, hft⟩ := len_bound hf
  obtain ⟨s, hs, _, hls⟩ := len_bound hl
  refine ⟨fun n => t (n + s n + 2), ht.comp ((PB.id'.add hs).add (PB.const 2)), fun x e he => ?_⟩
  refine (hft (x, e)).trans (hm ?_)
  rw [len_pair]
  have := (len_le_of_mem he).trans (hls x)
  omega
end Groundwork.PolyT

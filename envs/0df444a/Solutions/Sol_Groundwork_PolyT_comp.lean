-- Prove2me | solution 1 for Groundwork.PolyT.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:46:55.251616+00:00
-- url     : https://prove2.me/submissions/0340e66d-3493-4a85-a8a0-708f6048da40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Basic
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_of
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution {f : β → γ} {g : α → β} (hf : PolyT f) (hg : PolyT g) : PolyT (fun x => f (g x)) := by
  obtain ⟨P, t, ht, mt, hP, lP⟩ := hf.elim
  obtain ⟨Q, s, hs, -, hQ, lQ⟩ := hg.elim
  refine PolyT.of (Q.seq P) (t := fun n => s n + t (s n)) (s := fun n => t (s n)) (hs.add (ht.comp hs)) (ht.comp hs)
    (fun x M A B N => ?_) fun x => ?_
  · exact (hQ x M A B N).seq ((hP (g x) M A B N).mono (mt (lQ x)))
  · exact (lP (g x)).trans (mt (lQ x))
end Groundwork.PolyT

-- Prove2me | solution 1 for Groundwork.PolyT.tagF_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:54:05.945931+00:00
-- url     : https://prove2.me/submissions/fdc6972d-4f8c-4c7d-baa4-b32f4abe5ab5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_TM_consF_within
import Theorems.Thm_Groundwork_TM_pushW_within


set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Turing
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution (b : Bool) (x : V) (M A B N : List Sym) :
    (tagF b).Within (st (code x ++ M) A B N) (2 * (code x).length + 9) (st (code (.cons (.bit b) x) ++ M) A B N) := by
  have c1 := pushW_within (code x ++ M) A B N [.bit b]
  have c2 := consF_within (.bit b) x M A B N
  refine (c1.seq c2).mono ?_
  have h1 : (code (.bit b)).length = 1 := rfl
  omega
end Groundwork.PolyT

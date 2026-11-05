-- Prove2me | solution 1 for Groundwork.PolyT.fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:53:51.039997+00:00
-- url     : https://prove2.me/submissions/ef6191cd-9778-4164-9a38-b42a35d870a3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Basic
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_of
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_TM_dropF_within
import Theorems.Thm_Groundwork_TM_swapF_within
import Theorems.Thm_Groundwork_TM_unconsF_within
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4

attribute [local fun_prop] Groundwork.PolyT.id'
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.comp
section
namespace Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
section ops
variable (M A B N : List Sym)
private theorem dropW (x : α) : dropF.Within (st (wd x ++ M) A B N) (len x + 1) (st M A B N) :=
  dropF_within (toV x) M A B N
private theorem swapW (x : α) (y : β) :
    swapF.Within (st (wd x ++ (wd y ++ M)) A B N) (2 * (len x + len y) + 4) (st (wd y ++ (wd x ++ M)) A B N) :=
  swapF_within (toV x) (toV y) M A B N
private theorem unconsW (x : α) (y : β) :
    unconsF.Within (st (wd (x, y) ++ M) A B N) (2 * (len x + len y) + 6) (st (wd x ++ (wd y ++ M)) A B N) :=
  unconsF_within (toV x) (toV y) M A B N
end ops
private theorem pb_lin (a b : ℕ) {t : ℕ → ℕ} (ht : PB t) : PB fun n => a * t n + b :=
  ((PB.const a).mul ht).add (PB.const b)
private theorem fst0 : PolyT (fun p : β × γ => p.1) := by
  refine PolyT.of ((unconsF.seq swapF).seq dropF) (t := fun n => (2 * n + 6) + (2 * n + 4) + (n + 1)) (s := fun n => n)
    (((pb_lin 2 6 PB.id').add (pb_lin 2 4 PB.id')).add (PB.id'.add (PB.const 1))) PB.id' ?_ ?_
  · rintro ⟨a, b⟩ M A B N
    have h := ((unconsW M A B N a b).seq (swapW M A B N a b)).seq (dropW (wd a ++ M) A B N b)
    refine h.mono ?_
    have h1 := len_pair a b
    omega
  · rintro ⟨a, b⟩
    have h1 := len_pair a b
    change len a ≤ len (a, b)
    omega
end Groundwork.PolyT
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution {f : α → β × γ} (hf : PolyT f) : PolyT (fun x => (f x).1) :=
  comp fst0 hf
end Groundwork.PolyT

-- Prove2me | solution 1 for Groundwork.PolyT.optionElim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:16:40.196112+00:00
-- url     : https://prove2.me/submissions/350a5cd5-9b75-4dc6-b32c-ea8257e772ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_Groundwork_PolyT_listCases
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_of_wd
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
import Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45


attribute [local fun_prop] Groundwork.PolyT.cond'
attribute [local fun_prop] Groundwork.PolyT.ite'
attribute [local fun_prop] Groundwork.PolyT.sumElim

set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Turing
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution {o : α → Option β} {d : α → γ} {f : α → β → γ} (ho : PolyT o) (hd : PolyT d)
    (hf : PolyT fun p : α × β => f p.1 p.2) : PolyT (fun x => (o x).elim (d x) (f x)) := by
  -- an option has the tree of the list of its elements
  have h1 : PolyT (fun x => (o x).toList) :=
    of_wd ho id (fun _ => rfl) (fun x => by show wd (o x).toList = wd (o x); cases o x <;> rfl)
  have h2 : PolyT fun p : α × β × List β => f p.1 p.2.1 :=
    comp (g := fun p : α × β × List β => (p.1, p.2.1)) hf (by fun_prop)
  exact (listCases (f := fun x e _ => f x e) h1 hd h2).congr (fun x => by cases o x <;> rfl)
end Groundwork.PolyT

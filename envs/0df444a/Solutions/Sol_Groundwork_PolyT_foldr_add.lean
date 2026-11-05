-- Prove2me | solution 1 for Groundwork.PolyT.foldr_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:35:32.869193+00:00
-- url     : https://prove2.me/submissions/2bbc2b68-4961-44af-b08f-dc9da1fa6f7a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_ToTuring_Lib_List1
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_foldl_add
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
import Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45



set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution {l : α → List ε} {a : α → γ} {g : α → ε → γ → γ} (hl : PolyT l) (ha : PolyT a)
    (hg : PolyT fun p : α × ε × γ => g p.1 p.2.1 p.2.2)
    (hB : ∃ b, PB b ∧ ∀ x c, ∀ e ∈ l x, len (g x e c) ≤ len c + b (len x)) :
    PolyT (fun x => (l x).foldr (g x) (a x)) := by
  obtain ⟨b, hb, hB⟩ := hB
  have hg' : PolyT fun p : α × γ × ε => g p.1 p.2.2 p.2.1 :=
    PolyT.comp (f := fun p : α × ε × γ => g p.1 p.2.1 p.2.2) (g := fun p : α × γ × ε => (p.1, p.2.2, p.2.1)) hg
      (by fun_prop)
  have h : PolyT (fun x => (l x).reverse.foldl (fun c e => g x e c) (a x)) :=
    foldl_add (g := fun x c e => g x e c) (reverse hl) ha hg'
      ⟨b, hb, fun x c e he => hB x c e (List.mem_reverse.1 he)⟩
  exact h.congr fun x => by rw [List.foldl_reverse]
end Groundwork.PolyT

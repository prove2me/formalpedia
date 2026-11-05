-- Prove2me | solution 1 for Groundwork.PolyT.prodMk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:53:52.074451+00:00
-- url     : https://prove2.me/submissions/ae8213df-d47d-4b16-b66c-ecd9125e8377

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Basic
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_of
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_TM_consF_within
import Theorems.Thm_Groundwork_TM_dupF_within
import Theorems.Thm_Groundwork_TM_swapF_within
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4

attribute [local fun_prop] Groundwork.PolyT.id'
attribute [local fun_prop] Groundwork.PolyT.const
section
namespace Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
section ops
variable (M A B N : List Sym)
private theorem dupW (x : α) :
    dupF.Within (st (wd x ++ M) A B N) (3 * len x + 3) (st (wd x ++ (wd x ++ M)) A B N) :=
  dupF_within (toV x) M A B N
private theorem swapW (x : α) (y : β) :
    swapF.Within (st (wd x ++ (wd y ++ M)) A B N) (2 * (len x + len y) + 4) (st (wd y ++ (wd x ++ M)) A B N) :=
  swapF_within (toV x) (toV y) M A B N
private theorem consW (x : α) (y : β) :
    consF.Within (st (wd x ++ (wd y ++ M)) A B N) (2 * (len x + len y) + 6) (st (wd (x, y) ++ M) A B N) :=
  consF_within (toV x) (toV y) M A B N
end ops
private theorem pb_lin (a b : ℕ) {t : ℕ → ℕ} (ht : PB t) : PB fun n => a * t n + b :=
  ((PB.const a).mul ht).add (PB.const b)
end Groundwork.PolyT
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution {f : α → β} {g : α → γ} (hf : PolyT f) (hg : PolyT g) : PolyT (fun x => (f x, g x)) := by
  obtain ⟨P, t, ht, -, hP, lP⟩ := hf.elim
  obtain ⟨Q, s, hs, -, hQ, lQ⟩ := hg.elim
  refine PolyT.of (((((dupF.seq P).seq swapF).seq Q).seq swapF).seq consF)
    (t := fun n => (3 * n + 3) + t n + (2 * (t n + n) + 4) + s n + (2 * (s n + t n) + 4) + (2 * (t n + s n) + 6))
    (s := fun n => t n + s n + 2)
    ((((((pb_lin 3 3 PB.id').add ht).add (pb_lin 2 4 (ht.add PB.id'))).add hs).add (pb_lin 2 4 (hs.add ht))).add
      (pb_lin 2 6 (ht.add hs)))
    ((ht.add hs).add (PB.const 2)) (fun x M A B N => ?_) fun x => ?_
  · have h := (((((dupW M A B N x).seq (hP x (wd x ++ M) A B N)).seq (swapW M A B N (f x) x)).seq
      (hQ x (wd (f x) ++ M) A B N)).seq (swapW M A B N (g x) (f x))).seq (consW M A B N (f x) (g x))
    refine h.mono ?_
    have h1 := lP x
    have h2 := lQ x
    omega
  · have h1 := lP x
    have h2 := lQ x
    rw [len_pair]
    omega
end Groundwork.PolyT

-- Prove2me | solution 1 for Groundwork.PolyT.const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:50:12.123985+00:00
-- url     : https://prove2.me/submissions/37fff834-817e-4b7c-916d-9622d87a3186

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Basic
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_of
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_TM_dropF_within
import Theorems.Thm_Groundwork_TM_pushW_within
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4

attribute [local fun_prop] Groundwork.PolyT.id'
section
namespace Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
section ops
variable (M A B N : List Sym)
private theorem dropW (x : α) : dropF.Within (st (wd x ++ M) A B N) (len x + 1) (st M A B N) :=
  dropF_within (toV x) M A B N
end ops
end Groundwork.PolyT
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution (b : β) : PolyT (fun _ : α => b) :=
  PolyT.of (dropF.seq (pushW (wd b))) (t := fun n => n + 1 + 1) (s := fun _ => len b)
    ((PB.id'.add (PB.const 1)).add (PB.const 1)) (PB.const _)
    (fun x M A B N => (dropW M A B N x).seq (pushW_within M A B N (wd b))) fun _ => le_rfl
end Groundwork.PolyT

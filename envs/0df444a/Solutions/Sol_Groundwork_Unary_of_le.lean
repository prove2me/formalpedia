-- Prove2me | solution 1 for Groundwork.Unary.of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:29:25.95729+00:00
-- url     : https://prove2.me/submissions/ce33a5ec-3c16-49ab-9506-463945c4a391

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open Groundwork Groundwork.Unary
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
variable {f g : α → ℕ}
namespace Groundwork.Unary
theorem _root_.solution (hg : Unary g) (hf : PolyT f) (h : ∀ c, f c ≤ g c) :
    Unary f :=
  (PolyT.take hf hg).congr fun c => by
    rw [List.take_replicate, Nat.min_eq_left (h c)]
end Groundwork.Unary

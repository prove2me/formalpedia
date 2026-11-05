-- Prove2me | solution 1 for Groundwork.PolyT.congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:45:21.568602+00:00
-- url     : https://prove2.me/submissions/e1020b9c-471b-421d-8c4e-71275c820f0e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Enc
import Definitions.Def_ToTuring_TM_Ops
import Definitions.Def_ToTuring_Bound
import Mathlib.Tactic.FunProp
import Definitions.Def_ToTuring_PolyT

set_option autoImplicit false
section
section
open Groundwork
open TM
namespace Groundwork
namespace PolyT
theorem _root_.solution {α β : Type} [Enc α] [Enc β] {f g : α → β} (h : PolyT f) (e : ∀ x, f x = g x) : PolyT g := by
  obtain rfl : f = g := funext e
  exact h
end PolyT
end Groundwork

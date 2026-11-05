-- Prove2me | solution 1 for Groundwork.Network.card_merge_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:44:26.640167+00:00
-- url     : https://prove2.me/submissions/369cb40c-4970-4aab-ad0f-a0994c9b7230

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_Groundwork_card_tuples


set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
open Groundwork.Network
namespace Groundwork.Network
theorem _root_.solution [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ)
    (G : J') : #((N.merge χ s₀ t₀).S G) = ∏ a with χ a = G, #(N.S a) :=
  card_tuples _ _ _
end Groundwork.Network

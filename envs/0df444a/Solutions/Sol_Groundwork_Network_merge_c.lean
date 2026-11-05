-- Prove2me | solution 1 for Groundwork.Network.merge_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:57:11.180876+00:00
-- url     : https://prove2.me/submissions/2bcbe751-c8b1-417a-8375-cfb10e569f02

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_ColouringNet

set_option autoImplicit false
section
open Groundwork Groundwork.Network
open Finset
variable {J J' σ τ : Type*}
namespace Groundwork.Network
theorem _root_.solution [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ)
    (t₀ : τ) (G G' : J') :
    (N.merge χ s₀ t₀).c G G' = ∑ a with χ a = G, ∑ b with χ b = G', N.c a b := by
  change ∑ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.c p.1 p.2 = _
  rw [sum_filter, Fintype.sum_prod_type, sum_filter]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : χ a = G
  · rw [if_pos ha, sum_filter]
    exact sum_congr rfl fun b _ => by simp [ha]
  · simp [ha]
end Groundwork.Network

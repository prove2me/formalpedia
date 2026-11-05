-- Prove2me | solution 1 for Groundwork.rowBot_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:08:06.88304+00:00
-- url     : https://prove2.me/submissions/4765b1be-cc16-4029-b3cd-507eb201dc0d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Cross_Cuts

set_option autoImplicit false
section
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {n i : ℕ} {β : Fin n → Bell} (h : singlets β < i) (p q : Bits n) : rowBit.Bot i β p q = 0 := by
  have hz : ∀ h : Bell, h ≠ (true, true) → ∀ p q, rowBit.bot1 h p q = 0 := by decide
  refine sum_eq_zero fun S hS => ?_
  have hc := (mem_powersetCard.1 hS).2
  have hex : ∃ k ∈ S, β k ≠ (true, true) := by
    by_contra hcon
    push Not at hcon
    have hsub : S ⊆ univ.filter fun k => β k = (true, true) := fun k hk => by simp [hcon k hk]
    have := card_le_card hsub
    unfold singlets at h
    omega
  obtain ⟨k, hk, hne⟩ := hex
  rw [prod_eq_zero hk (hz _ hne _ _), zero_mul]
end Groundwork

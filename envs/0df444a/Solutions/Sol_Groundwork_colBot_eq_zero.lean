-- Prove2me | solution 1 for Groundwork.colBot_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:08:41.723217+00:00
-- url     : https://prove2.me/submissions/a23db514-5d21-48d5-9e21-36e587894e50

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
theorem _root_.solution {n i : ℕ} {β : Fin n → Bell} (h : i < others β) (p q : Bits n) : colBit.Bot i β p q = 0 := by
  have hz : ∀ h : Bell, h ≠ (false, false) → ∀ p q, colBit.bot0 h p q = 0 := by decide
  refine sum_eq_zero fun S hS => ?_
  have hc := (mem_powersetCard.1 hS).2
  have hex : ∃ k ∈ Sᶜ, β k ≠ (false, false) := by
    by_contra hcon
    push Not at hcon
    have hsub : (univ.filter fun k => β k ≠ (false, false)) ⊆ S := fun k hk => by
      by_contra hkS
      exact (mem_filter.1 hk).2 (hcon k (mem_compl.2 hkS))
    have := card_le_card hsub
    unfold others at h
    omega
  obtain ⟨k, hk, hne⟩ := hex
  rw [prod_eq_zero hk (hz _ hne _ _), mul_zero]
end Groundwork

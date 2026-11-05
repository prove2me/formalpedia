-- Prove2me | solution 1 for Groundwork.cross_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:07:43.086351+00:00
-- url     : https://prove2.me/submissions/95c47abc-90a4-4bb5-9b13-3408c555bbbf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Groundwork_Cross_Bit

set_option autoImplicit false
section
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {n : ℕ} (x y u v : Bits n) : cross x y u v = ∏ k, X₁ (x k) (y k) (u k) (v k) := by
  by_cases h : x = v ∧ y = u
  · obtain ⟨rfl, rfl⟩ := h
    simp [cross, X₁]
  · rw [cross, if_neg h]
    have hex : ∃ k, ¬ (x k = v k ∧ y k = u k) := by
      by_contra hc
      push Not at hc
      exact h ⟨funext fun k => (hc k).1, funext fun k => (hc k).2⟩
    obtain ⟨k, hk⟩ := hex
    exact (prod_eq_zero (mem_univ k) (by simp only [X₁, if_neg hk])).symm
end Groundwork

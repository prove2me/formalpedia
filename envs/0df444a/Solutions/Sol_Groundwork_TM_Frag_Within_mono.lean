-- Prove2me | solution 1 for Groundwork.TM.Frag.Within.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:20:28.165304+00:00
-- url     : https://prove2.me/submissions/c7921e59-d26c-4f3d-8f38-de70f73a7ebe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Run
import Definitions.Def_ToTuring_TM_Frag
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}
attribute [instance] Frag.fin
variable {τ : Type}
namespace Groundwork.TM
namespace Frag.Within
theorem _root_.solution {P : Frag Γ (Option τ)} {S S' : ∀ k, List (Γ k)} {t t' : ℕ} (h : P.Within S t S') (ht : t ≤ t') :
    P.Within S t' S' := by
  obtain ⟨n, hn, hr⟩ := h
  exact ⟨n, hn.trans ht, hr⟩
end Frag.Within
end Groundwork.TM

-- Prove2me | solution 1 for Groundwork.TM.Frag.Within.seq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:05.058914+00:00
-- url     : https://prove2.me/submissions/3515cb2a-8300-4d91-9b9c-beb68c72a1b1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Run
import Definitions.Def_ToTuring_TM_Frag
import Theorems.Thm_Groundwork_TM_Frag_seq_runs

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
theorem _root_.solution {P Q : Frag Γ (Option τ)} {S S' S'' : ∀ k, List (Γ k)} {t t' : ℕ} (h : P.Within S t S')
    (h' : Q.Within S' t' S'') : (P.seq Q).Within S (t + t') S'' := by
  obtain ⟨n, hn, hr⟩ := h
  obtain ⟨n', hn', hr'⟩ := h'
  exact ⟨n + n', Nat.add_le_add hn hn', Frag.seq_runs hr hr'⟩
end Frag.Within
end Groundwork.TM

-- Prove2me | solution 1 for Groundwork.TM.run_place
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:03:34.786567+00:00
-- url     : https://prove2.me/submissions/de41797c-dbfa-4454-b160-1dd740ccf0f1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_ToTuring_TM_Run
import Theorems.Thm_Groundwork_TM_stepAux_place

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}
variable {Λ Λ' : Type} (ι : Λ → Λ') (e : Option Λ')
namespace Groundwork.TM
theorem _root_.solution {M : Λ → TM2.Stmt Γ Λ σ} {M' : Λ' → TM2.Stmt Γ Λ' σ} (hM : ∀ l, M' (ι l) = place ι e (M l)) :
    ∀ {n : ℕ} {a b : TM2.Cfg Γ Λ σ}, Run (TM2.step M) a n b → Run (TM2.step M') (placeCfg ι e a) n (placeCfg ι e b)
  | 0, _, _, h => by cases h; exact rfl
  | n + 1, ⟨none, v, S⟩, b, ⟨c, hc, _⟩ => by simp [TM2.step] at hc
  | n + 1, ⟨some l, v, S⟩, b, ⟨c, hc, h⟩ => by
    refine ⟨placeCfg ι e c, ?_, solution hM h⟩
    simp only [TM2.step, Option.some.injEq] at hc
    simp only [placeCfg, Option.elim, Function.comp, TM2.step, hM, stepAux_place, hc]
end Groundwork.TM

-- Prove2me | solution 1 for Groundwork.TM.stepAux_place
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:02:50.821456+00:00
-- url     : https://prove2.me/submissions/6b1121a3-517a-4935-b541-de4a7d25eb0c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_ToTuring_TM_Run

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}
variable {Λ Λ' : Type} (ι : Λ → Λ') (e : Option Λ')
namespace Groundwork.TM
theorem _root_.solution (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.stepAux (place ι e q) v S = placeCfg ι e (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih _ _
  | branch p _ _ ih₁ ih₂ => simp only [place, TM2.stepAux, ih₁, ih₂]; cases p v <;> rfl
  | goto => rfl
  | halt => cases e <;> rfl
end Groundwork.TM

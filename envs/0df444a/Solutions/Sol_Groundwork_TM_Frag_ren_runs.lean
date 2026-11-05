-- Prove2me | solution 1 for Groundwork.TM.Frag.ren_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:44:23.280225+00:00
-- url     : https://prove2.me/submissions/4ca069e5-855d-4e5c-8e7b-2b50fbdb5ca1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Frag
import Definitions.Def_ToTuring_TM_Rename
import Theorems.Thm_Groundwork_TM_run_renK

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {A Λ σ : Type} (φ : K₁ → K₂)
namespace Groundwork.TM
namespace Frag
theorem _root_.solution (hφ : Function.Injective φ) {P : Frag (fun _ : K₁ => A) σ} {v : σ} {T T' : K₁ → List A} {n : ℕ}
    (h : P.Runs v T n T') {S S' : K₂ → List A} (hS : ∀ k, S (φ k) = T k) (hS' : ∀ k, S' (φ k) = T' k)
    (ho : ∀ k, (∀ a, φ a ≠ k) → S' k = S k) : (P.ren φ).Runs v S n S' :=
  run_renK hφ h hS hS' ho
end Frag
end Groundwork.TM

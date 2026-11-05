-- Prove2me | solution 1 for Groundwork.Grid.ZG_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:56:01.52782+00:00
-- url     : https://prove2.me/submissions/41f70e73-f28a-4b13-a7c4-279a52a88d51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_Digits

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect)
namespace Groundwork.Grid
theorem _root_.solution {ρ γ α : Type} [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
    (R : Inst (ρ × γ) α) {G G' : Rect ρ γ → α → α → α → α → ℤ} (h : ∀ ω ∈ Ω ρ γ, G ω = G' ω) : ZG R G = ZG R G' := by
  unfold ZG
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.prod_congr rfl fun ω hω => show app (G ω) ℓ ω = app (G' ω) ℓ ω by rw [h ω hω]]
end Groundwork.Grid

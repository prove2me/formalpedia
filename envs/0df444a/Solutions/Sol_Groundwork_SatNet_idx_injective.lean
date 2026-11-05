-- Prove2me | solution 1 for Groundwork.SatNet.idx_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:57:12.3367+00:00
-- url     : https://prove2.me/submissions/496f7c11-62d3-4f12-a555-b5f44057b5b3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_StepMachines_Math_SatNet
import Theorems.Thm_Groundwork_SatNet_mul_add_inj

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
namespace Groundwork.SatNet
theorem _root_.solution {g μ k : ℕ} : Function.Injective (idx (g := g) (μ := μ) (k := k)) := by
  rintro ⟨a, c, j⟩ ⟨a', c', j'⟩ h
  obtain ⟨h1, h2⟩ := mul_add_inj j.2 j'.2 h
  obtain ⟨h3, h4⟩ := mul_add_inj c.2 c'.2 h1
  simp only [Prod.mk.injEq]
  exact ⟨Fin.ext h3, Fin.ext h4, Fin.ext h2⟩
end Groundwork.SatNet

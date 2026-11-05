-- Prove2me | solution 1 for Groundwork.Prog.capF_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:34:03.779403+00:00
-- url     : https://prove2.me/submissions/68014dc0-77f5-44d2-9794-f68305e28f19

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatArith
import Definitions.Def_StepMachines_Prog_Count
import Theorems.Thm_Groundwork_Prog_Count_sized_wordNet


set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset Groundwork.Prog.Count
namespace Groundwork.Prog
theorem _root_.solution {g k : ℕ} (hg : 0 < g) (φ : Fml) {a b : Fin g} (hab : a ≠ b) :
    capF g k φ a.val b.val ≤ 2 * (mu g φ * k) := by
  have h := (sized_wordNet (k := k) (φ := φ) hg 0).sum_c a
  have h1 : (wordNet g k φ).c a b ≤ ∑ b ∈ univ.erase a, (wordNet g k φ).c a b :=
    Finset.single_le_sum (f := fun b => (wordNet g k φ).c a b) (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.2 ⟨hab.symm, mem_univ b⟩)
  have h2 : 2 * k * mu g φ = 2 * (mu g φ * k) := by ring
  have h3 : (wordNet g k φ).c a b = capF g k φ a.val b.val := rfl
  omega
end Groundwork.Prog

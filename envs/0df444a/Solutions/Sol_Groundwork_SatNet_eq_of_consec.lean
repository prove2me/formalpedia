-- Prove2me | solution 1 for Groundwork.SatNet.eq_of_consec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:56:29.439698+00:00
-- url     : https://prove2.me/submissions/335f6384-ebd8-41ff-9484-00be9eafac67

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

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {ι V : Type}
variable {idx : ι → ℕ} {lab : ι → Option V}
namespace Groundwork.SatNet
theorem _root_.solution (hidx : Function.Injective idx) {z : ι → Bool}
    (hz : ∀ p q, Consec idx lab p q → z p = z q) {p q : ι} (hp : lab p ≠ none) (hpq : lab p = lab q) :
    z p = z q := by
  have key : ∀ n p q, idx p < idx q → idx q - idx p ≤ n → lab p ≠ none → lab p = lab q → z p = z q := by
    intro n
    induction n with
    | zero => intro p q h1 h2; omega
    | succ n ih =>
      intro p q h1 h2 hp hpq
      by_cases h : ∃ r, idx p < idx r ∧ idx r < idx q ∧ lab r = lab p
      · obtain ⟨r, hr1, hr2, hr3⟩ := h
        exact (ih p r hr1 (by omega) hp hr3.symm).trans
          (ih r q hr2 (by omega) (hr3 ▸ hp) (hr3.trans hpq))
      · exact hz p q ⟨h1, hp, hpq, fun r a b c => h ⟨r, a, b, c⟩⟩
  rcases lt_trichotomy (idx p) (idx q) with hlt | heq | hgt
  · exact key _ p q hlt le_rfl hp hpq
  · rw [hidx heq]
  · exact (key _ q p hgt le_rfl (hpq ▸ hp) hpq.symm).symm
end Groundwork.SatNet

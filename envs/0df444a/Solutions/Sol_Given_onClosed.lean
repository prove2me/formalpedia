-- Prove2me | solution 1 for Given.onClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:46:31.162614+00:00
-- url     : https://prove2.me/submissions/8a9e8243-2bc1-42ec-9a90-991918eeca85

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GivenStatement
import Definitions.Def_Printed_LevelFrom
import Definitions.Def_Printed_Count
import Mathlib.Tactic
import Definitions.Def_Given_Networks
import Theorems.Thm_Given_stOnGiven
import Theorems.Thm_Printed_networkOn_close
import Theorems.Thm_QueryMachines_stClose


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed
variable {Q A C : Type}
namespace Given
theorem _root_.solution {NM : NetMachine} {C₁ g K : ℕ} {e : ℝ} (hNM : ComputesNetworks NM C₁ g K e) [Enc Q] [Enc A] [HasSize C] [Enc C] [Carried C] {Np : ProcsQ Q A C} {O : Q → Option A} {c : C} {N : Net g} {P B τ S : ℕ}
    (h : IsGivenNetwork Np O c N P B τ S) :
    ∃ T : ℕ, (networkOnSteps g NM (Np.close O)).Runs c T (size c + C₁ * (P + B) ^ C₁ + S + 4) N.value ∧
      (T : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ (e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ C₁) * τ := by
  obtain ⟨T, h1, h2⟩ := (stOnGiven NM C₁ g K e hNM Q A C Np O c N P B τ S h).2
  refine ⟨T, ?_, h2⟩
  rw [← networkOn_close]
  exact (stClose _ _ _ _ _ _ _ _ _ _).2 h1
end Given

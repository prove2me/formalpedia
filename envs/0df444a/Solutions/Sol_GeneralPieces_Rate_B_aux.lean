-- Prove2me | solution 1 for GeneralPieces.Rate.B_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:46:19.284649+00:00
-- url     : https://prove2.me/submissions/0d82e06a-85f0-4868-8a1c-9a9d3b331bb3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (k a q lam B₁ : ℕ) (hk : 8 ≤ k) (ha : 4 ≤ a) (hq : q * k ≤ 2 * a) :
    1 * (a * a ^ 2 * lam) * q + B₁ * (q + q * q) * k ≤ a ^ 4 * lam + a ^ 2 * B₁ := by
  have h8 : q * 8 ≤ q * k := Nat.mul_le_mul_left _ hk
  have h1 : q ≤ a := by omega
  have h2 : 2 * (1 + q) ≤ a := by omega
  have h3 : (q + q * q) * k ≤ a ^ 2 := by
    calc (q + q * q) * k = (1 + q) * (q * k) := by ring
      _ ≤ (1 + q) * (2 * a) := Nat.mul_le_mul_left _ hq
      _ = 2 * (1 + q) * a := by ring
      _ ≤ a * a := Nat.mul_le_mul_right _ h2
      _ = a ^ 2 := by ring
  calc 1 * (a * a ^ 2 * lam) * q + B₁ * (q + q * q) * k = a * a ^ 2 * lam * q + B₁ * ((q + q * q) * k) := by ring
    _ ≤ a * a ^ 2 * lam * a + B₁ * a ^ 2 := by gcongr
    _ = a ^ 4 * lam + a ^ 2 * B₁ := by ring
end GeneralPieces.Rate

-- Prove2me | solution 1 for GeneralPieces.Rate.L_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:46:14.764759+00:00
-- url     : https://prove2.me/submissions/efacfa29-6d43-4825-a609-f2f20648a393

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
theorem _root_.solution (D k a R u lam S : ℕ) (hD : 3 ≤ D) (hk : 2 ≤ k) (hS : S ≤ a ^ 4 * lam) (hR : 4 * R ≤ a ^ 4) (hu : u ≤ 4 * lam) :
    (D * (S + R * u) + 3 * a ^ 2 * (a ^ 2 * (1 * lam))) / (D * k ^ 2) ≤ a ^ 4 * lam := by
  apply Nat.div_le_of_le_mul
  have h1 : R * u ≤ a ^ 4 * lam := by
    calc R * u ≤ R * (4 * lam) := Nat.mul_le_mul_left _ hu
      _ = 4 * R * lam := by ring
      _ ≤ a ^ 4 * lam := Nat.mul_le_mul_right _ hR
  have h2 : 3 ≤ k ^ 2 := by nlinarith
  calc D * (S + R * u) + 3 * a ^ 2 * (a ^ 2 * (1 * lam))
      = D * (S + R * u) + 3 * (a ^ 4 * lam) := by ring
    _ ≤ D * (a ^ 4 * lam + a ^ 4 * lam) + D * (a ^ 4 * lam) := by gcongr
    _ = D * 3 * (a ^ 4 * lam) := by ring
    _ ≤ D * k ^ 2 * (a ^ 4 * lam) := by gcongr
end GeneralPieces.Rate

-- Prove2me | solution 1 for GeneralPieces.Rate.le_of_K_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:19.913759+00:00
-- url     : https://prove2.me/submissions/f2f605bd-e39b-4f83-8a58-ec23d20fa973

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
theorem _root_.solution (k v N e' : ℝ) (hk : 0 < k) (h3 : 3 ≤ e' * k) (hN : 0 ≤ N) (hv : k * v ≤ 3 * N) : v ≤ e' * N := by
  have h : k * v ≤ k * (e' * N) := by
    calc k * v ≤ 3 * N := hv
      _ ≤ e' * k * N := mul_le_mul_of_nonneg_right h3 hN
      _ = k * (e' * N) := by ring
  exact le_of_mul_le_mul_left h hk
end GeneralPieces.Rate

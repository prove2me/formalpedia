-- Prove2me | solution 1 for GeneralPieces.Remarks.conditions_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:17:21.533228+00:00
-- url     : https://prove2.me/submissions/75b5cf3a-94fe-4386-b920-4f3dd22b9afc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_GeneralPieces_Num_Remarks

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Remarks
open Finset Levels.Gen ClauseBound.Gen AppRunningTime
namespace GeneralPieces.Remarks
theorem _root_.solution (k K₀ : ℕ) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → K₀ ^ 17 ≤ n ∧ (k : ℝ) ≤ Real.logb 2 n ^ (1 / 4 : ℝ) := by
  refine ⟨max (K₀ ^ 17) (2 ^ k ^ 4), fun n hn => ⟨le_trans (le_max_left _ _) hn, ?_⟩⟩
  have h1 : 2 ^ k ^ 4 ≤ n := le_trans (le_max_right _ _) hn
  have h2 : ((k ^ 4 : ℕ) : ℝ) ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast lt_of_lt_of_le (by positivity) h1), Real.rpow_natCast]
    exact_mod_cast h1
  have h3 : (((k ^ 4 : ℕ) : ℝ)) ^ (1 / 4 : ℝ) = k := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [← h3]
  exact Real.rpow_le_rpow (by positivity) h2 (by norm_num)
end GeneralPieces.Remarks

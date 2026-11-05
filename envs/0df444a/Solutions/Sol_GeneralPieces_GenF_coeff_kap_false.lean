-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_kap_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:06:53.442859+00:00
-- url     : https://prove2.me/submissions/6393eb51-4ba7-42a5-a83f-fb358cb0e6fc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
import Theorems.Thm_GeneralPieces_GenF_entry_false

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (α : X →₀ ℕ) : coeff α (kap false) = algebraMap ℚ S (coeff α kapQ) * epsP ^ wtX α := by
  change (if α.degree = 2 then ∑ i ∈ α.support, ∑ i' ∈ α.support, sel false (fun p => sel false 0 (fun q => kapS p q) i') 0 i else 0) =
    algebraMap ℚ S (if α.degree = 2 then ∑ i ∈ α.support, ∑ i' ∈ α.support, GamX i i' else 0) * _
  split_ifs with h
  · rw [map_sum, sum_mul]
    refine sum_congr rfl fun i hi => ?_
    rw [map_sum, sum_mul]
    exact sum_congr rfl fun i' hi' => entry_false h hi hi'
  · rw [map_zero, zero_mul]
end GeneralPieces.GenF

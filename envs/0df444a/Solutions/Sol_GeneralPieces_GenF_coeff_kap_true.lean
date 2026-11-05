-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_kap_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:07:32.987175+00:00
-- url     : https://prove2.me/submissions/7750de2b-f5d7-4ba2-989f-3e270dd19b70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
import Theorems.Thm_GeneralPieces_GenF_entry_true

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (α : X →₀ ℕ) : coeff α (kap true) = algebraMap ℚ S (coeff α kapQ) * epsM ^ wtX α := by
  change (if α.degree = 2 then ∑ i ∈ α.support, ∑ i' ∈ α.support, sel true (fun p => sel true 0 (fun q => kapS p q) i') 0 i else 0) =
    algebraMap ℚ S (if α.degree = 2 then ∑ i ∈ α.support, ∑ i' ∈ α.support, GamX i i' else 0) * _
  split_ifs with h
  · rw [sum_comm (f := fun i i' => GamX i i'), map_sum, sum_mul]
    refine sum_congr rfl fun i hi => ?_
    rw [map_sum, sum_mul]
    exact sum_congr rfl fun i' hi' => entry_true h hi hi'
  · rw [map_zero, zero_mul]
end GeneralPieces.GenF

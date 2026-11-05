-- Prove2me | solution 1 for GeneralPieces.Level.zetaOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:22.013839+00:00
-- url     : https://prove2.me/submissions/af68c918-715d-4369-ab92-3d5f0b4a65c6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Level
import Definitions.Def_GeneralPieces_Rec_Level

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Level
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.Level Finset
namespace GeneralPieces.Level
theorem _root_.solution {s : Step} (hD : 2 ≤ s.D) : 0 < zetaOf s ∧ zetaOf s ≤ 1 := by
  have hDr : (2 : ℝ) ≤ s.D := by exact_mod_cast hD
  unfold zetaOf
  exact ⟨by positivity, by rw [div_le_one (by positivity)]; linarith⟩
end GeneralPieces.Level

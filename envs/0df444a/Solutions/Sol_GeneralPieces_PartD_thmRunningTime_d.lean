-- Prove2me | solution 1 for GeneralPieces.PartD.thmRunningTime_d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:19:30.915611+00:00
-- url     : https://prove2.me/submissions/66760e09-252d-4c01-b6e3-0ecb0d93a636

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_PaddedDescent_Main
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartD
import Theorems.Thm_GeneralPieces_PartD_alpha_mem
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_Sat3_inRateTM


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartD
namespace GeneralPieces.PartD
theorem _root_.solution (ρ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) : Sat3.InRateTM (Real.logb 2 (1 / ρ) / 10) :=
  Sat3.inRateTM.mono (by linarith [(alpha_mem ρ hρ hρ1).2])
end GeneralPieces.PartD

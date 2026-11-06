-- Prove2me | solution 1 for GeneralPieces.stSpec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:07:20.723244+00:00
-- url     : https://prove2.me/submissions/12f432a9-fac8-4d91-8dc8-b6d4c76e9501

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_Consts
import Definitions.Def_GeneralPieces_Half_Size
import Definitions.Def_GeneralPieces_Trim_Prog
import Definitions.Def_ClauseBound_Inst_HalfAll
import Definitions.Def_GeneralPieces_Half_Spec
import Theorems.Thm_GeneralPieces_half_realizes
import Theorems.Thm_ClauseBound_Inst_Half_hF_eq
import Theorems.Thm_ClauseBound_Inst_Rec_factN_eq
import Theorems.Thm_ClauseBound_Part_two_le_hOf


set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half Finset
namespace GeneralPieces
theorem _root_.solution (hPF : AppHalfPieces.PieceFacts) : StSpec := by
  intro c₀ c lam h' hl hC
  have hhF : hF c₀ lam = ClauseBound.Part.hOf lam := hF_eq hC.h_le
  refine ⟨Nat.succ_pos _, ?_, ?_, fun tr i _ => min_le_left _ _, halfA lam, half_realizes hPF h' hl hC⟩
  · change 1 ≤ factN (hF c₀ lam)
    rw [factN_eq]
    exact Nat.factorial_pos _
  · change 1 ≤ c
    by_contra h0
    have h1 : c = 0 := by omega
    have h2 := hC.cnt
    have h3 := ClauseBound.Part.two_le_hOf lam
    rw [h1, pow_zero] at h2
    omega
end GeneralPieces

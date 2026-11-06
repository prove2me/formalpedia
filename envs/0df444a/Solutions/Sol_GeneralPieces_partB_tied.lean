-- Prove2me | solution 1 for GeneralPieces.partB_tied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:41:13.292142+00:00
-- url     : https://prove2.me/submissions/4db8cef8-f563-47e6-bec9-838840007285

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_Defs
import Definitions.Def_GeneralPieces_Rec_Seq
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Rec_Descend
import Definitions.Def_GeneralPieces_Rec_Level
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_ClauseBound_Alg_Enum
import Definitions.Def_ClauseBound_Alg_Grid
import Definitions.Def_ClauseBound_Alg_CertEnum
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_Alg_CertLevel
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_GeneralPieces_Rec_PartB
import Theorems.Thm_GeneralPieces_partB_tied_of
import Theorems.Thm_GeneralPieces_solveG2
import Theorems.Thm_GeneralPieces_certSolveG
import Theorems.Thm_ClauseBound_Alg_Need_stNeedG
import Theorems.Thm_GeneralPieces_Chain_stChain2
import Theorems.Thm_GeneralPieces_stRate2


set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen
namespace GeneralPieces
theorem _root_.solution (c : ℕ) : ∃ C₀ : ℕ, ∀ (P : PiecesF) (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → Par P ρ c → P.m = 1 → P.Keeps → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
    Tied.PartB P ρ x₀ C₀ :=
  partB_tied_of stRate2 Chain.stChain2 solveG2 Need.stNeedG certSolveG c
end GeneralPieces

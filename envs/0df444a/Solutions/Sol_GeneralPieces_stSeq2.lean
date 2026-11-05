-- Prove2me | solution 1 for GeneralPieces.stSeq2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:47:52.235392+00:00
-- url     : https://prove2.me/submissions/134566df-ea35-4c66-9c3f-2908697125c4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_GeneralPieces_Rec_Seq
import Theorems.Thm_GeneralPieces_stSeq2_of
import Theorems.Thm_ClauseBound_Alg_Need_stNeedG
import Theorems.Thm_ClauseBound_Gen_Pick_stPick
import Theorems.Thm_GeneralPieces_stRate2
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen
namespace GeneralPieces
theorem _root_.solution (hChain : StChain2) (hSolve : ∀ P, StSolveG2 P) : StSeq2 :=
  stSeq2_of hChain stRate2 Pick.stPick hSolve Need.stNeedG
end GeneralPieces

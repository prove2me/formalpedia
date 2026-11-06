-- Prove2me | solution 1 for GeneralPieces.certSolveG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:27:43.120603+00:00
-- url     : https://prove2.me/submissions/3f247d72-91b9-436b-8d5a-8acdc618a973

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
import Theorems.Thm_ClauseBound_Alg_CertEnum_stCertBruteK
import Theorems.Thm_ClauseBound_Alg_CertEnum_stCertEnum
import Theorems.Thm_ClauseBound_Alg_CertGridG_stCertGrid
import Theorems.Thm_ClauseBound_Alg_CertGridG_stCertLam
import Theorems.Thm_ClauseBound_Alg_CertLevel_stCertExpandG
import Theorems.Thm_ClauseBound_Alg_CertLevel_stCertSolveG
import Theorems.Thm_PaddedDescent_F_certRebalG


set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen
namespace GeneralPieces
theorem _root_.solution (P : PiecesF) : StCertSolveG P :=
  CertLevel.stCertSolveG P (CertGridG.stCertLam P)
    (CertLevel.stCertExpandG P (CertGridG.stCertGrid P) (CertGridG.stCertLam P) CertEnum.stCertEnum PaddedDescent.F.certRebalG) CertEnum.stCertBruteK
end GeneralPieces

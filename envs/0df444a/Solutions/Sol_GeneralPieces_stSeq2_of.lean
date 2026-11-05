-- Prove2me | solution 1 for GeneralPieces.stSeq2_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:16.948939+00:00
-- url     : https://prove2.me/submissions/b2db1dbf-14b1-488e-ad30-9c8877109098

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
import Theorems.Thm_GeneralPieces_seq_of_pick
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen
namespace GeneralPieces
theorem _root_.solution (hCh : StChain2) (hR : StRate2) (hPk : StPick) (hSolve : ∀ P, StSolveG2 P) (hNeed : ∀ P, StNeedG P) : StSeq2 := by
  intro P ρ c x₀ hρ hρ1 hP hm hx hx2
  obtain ⟨pick, hp1, hp2, hp3, hp4⟩ := hPk P x₀
  obtain ⟨C₀, Q, hQ, -⟩ := seq_of_pick hCh hR hSolve hNeed P ρ c x₀ hρ hρ1 hP hm hx hx2 pick hp1 hp2 hp3 hp4
  exact ⟨C₀, Q, hQ⟩
end GeneralPieces

-- Prove2me | solution 1 for GeneralPieces.pick_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:56:38.215853+00:00
-- url     : https://prove2.me/submissions/46543d1a-4813-4e14-9905-7293b343a01f

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
import Theorems.Thm_GeneralPieces_K_strictMono
import Theorems.Thm_GeneralPieces_pick_spec
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen
namespace GeneralPieces
theorem _root_.solution (P : PiecesF) (x₀ : ℕ) (hx : 18 ≤ x₀) (l lam B : ℕ) (I : PInst) (hI : WFe (K x₀ l) lam B I) :
    (Pick.pick P x₀ (List.replicate I.2.length ())).2 = idx P x₀ l := by
  obtain ⟨-, hp2, hp3, hp4⟩ := pick_spec P x₀
  have hmono := K_strictMono x₀ hx
  obtain ⟨b, hb⟩ : ∃ b : U, b = List.replicate I.2.length () := ⟨_, rfl⟩
  have hbl : b.length = K x₀ l := by rw [hb, List.length_replicate, hI.1.rows]
  have h3 := hp3 b (by rw [hbl]; exact hmono.monotone (Nat.zero_le l))
  have h4 := hp4 b
  rw [hbl] at h3 h4
  have hl : (Pick.pick P x₀ b).1.length = l := by
    have a1 := hmono.le_iff_le.1 h3
    have a2 := hmono.lt_iff_lt.1 h4
    omega
  rw [← hb, hp2, hl]
end GeneralPieces

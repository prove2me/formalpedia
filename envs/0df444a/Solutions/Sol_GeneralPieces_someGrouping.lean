-- Prove2me | solution 1 for GeneralPieces.someGrouping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:21:50.891719+00:00
-- url     : https://prove2.me/submissions/988476ac-ec00-4f7e-921e-26c5d2ace0a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Group_CaseI
import Definitions.Def_GeneralPieces_Group_CaseII
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_CertG
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_GeneralPieces_Group_Lemma
import Theorems.Thm_GeneralPieces_Group_exists_grouping_lt

set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork PaddedDescent.F ClauseBound.Alg GeneralPieces.Group
namespace GeneralPieces
theorem _root_.solution : AppRunningTime.SomeGrouping := by
  intro K g ζ P c hK hg hζ0 hζ1 hP1 hs hP h
  obtain ⟨χ, h1, h2⟩ := exists_grouping_lt K g ζ P c hK hg hζ0 hζ1 hs hP h
  exact ⟨χ, fun γ => (h1 γ).le, h2⟩
end GeneralPieces

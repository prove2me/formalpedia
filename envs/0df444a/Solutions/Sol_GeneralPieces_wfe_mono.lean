-- Prove2me | solution 1 for GeneralPieces.wfe_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:54:36.103084+00:00
-- url     : https://prove2.me/submissions/a747e21f-1ce7-42d9-8b05-9dd73e8ce667

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
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork PaddedDescent.F ClauseBound.Alg GeneralPieces.Group
namespace GeneralPieces
theorem _root_.solution {K lam B B' : ℕ} {J : PInst} (h : WFe K lam B J) (hB : B ≤ B') : WFe K lam B' J :=
  ⟨⟨h.1.lam_pos, h.1.lam_le, h.1.rows, h.1.row_len, fun r hr z hz => (h.1.abs_le r hr z hz).trans (Nat.pow_le_pow_right (by norm_num) hB)⟩, h.2⟩
end GeneralPieces

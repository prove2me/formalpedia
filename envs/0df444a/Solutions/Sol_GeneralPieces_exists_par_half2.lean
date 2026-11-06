-- Prove2me | solution 1 for GeneralPieces.exists_par_half2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:16:41.414084+00:00
-- url     : https://prove2.me/submissions/e2d85efd-a75d-4fd8-8fb4-0c4f7f22af86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_Consts
import Definitions.Def_GeneralPieces_Half_Size
import Definitions.Def_GeneralPieces_Trim_Prog
import Definitions.Def_ClauseBound_Inst_HalfAll
import Definitions.Def_GeneralPieces_Half_Spec
import Theorems.Thm_GeneralPieces_stSpec
import Theorems.Thm_ClauseBound_Inst_Half_Par_par_of_cst
import Theorems.Thm_GeneralPieces_exists_cst2
import Theorems.Thm_GeneralPieces_thmHalfPiecesPure


set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half Finset
namespace GeneralPieces
theorem _root_.solution (hPF : AppHalfPieces.PieceFacts) :
    ∃ c₀ c : ℕ, ClauseBound.Gen.Par (halfF c₀ c) (1 / Real.sqrt 2) c ∧ ∀ lam : ℕ, 1 ≤ lam → Cst c₀ c lam := by
  obtain ⟨c₀, c, hC⟩ := exists_cst2 (thmHalfPiecesPure hPF)
  exact ⟨c₀, c, ClauseBound.Inst.Half.Par.par_of_cst (stSpec hPF) hC, hC⟩
end GeneralPieces

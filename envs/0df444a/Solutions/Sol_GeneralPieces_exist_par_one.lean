-- Prove2me | solution 1 for GeneralPieces.exist_par_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:36:11.960514+00:00
-- url     : https://prove2.me/submissions/f316f073-8fea-4fb9-94aa-eec17992da5c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_DefGenPieces_MayAssume
import Theorems.Thm_GeneralPieces_mayAssume
import Theorems.Thm_GeneralPieces_to_par_one


set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
open DefGenPieces Trim
namespace GeneralPieces
theorem _root_.solution {ρ : ℝ} {c : ℕ} (h : Exist ρ c) : ∃ P : PiecesF, Par P ρ c ∧ P.Keeps ∧ P.m = 1 :=
  let ⟨P, A', val, hP⟩ := h
  let ⟨_, hP', _, hcap⟩ := mayAssume ρ c P A' val hP
  ⟨_, to_par_one hP' fun tr lam i _ _ => hcap tr lam i⟩
end GeneralPieces

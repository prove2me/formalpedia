-- Prove2me | solution 1 for GeneralPieces.DefGenPieces.sum_bitsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:43.562865+00:00
-- url     : https://prove2.me/submissions/c8aff996-b017-4472-9c3e-deae90b99d61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Theorems.Thm_GeneralPieces_Trim_exists_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] GeneralPieces.Trim.length_bitsOf
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
open GeneralPieces.DefGenPieces
open Trim
namespace GeneralPieces.DefGenPieces
theorem _root_.solution {n : ℕ} (G : List Bool → ℤ) : ∑ θ : Pieces.Bits n, G (bitsOf θ) = ∑ w ∈ words n, G w :=
  Finset.sum_nbij bitsOf (fun θ _ => mem_words.2 (length_bitsOf θ)) (fun _ _ _ _ e => List.ofFn_injective e)
    (fun _ hw => let ⟨x, hx⟩ := exists_bitsOf (mem_words.1 (Finset.mem_coe.1 hw)); ⟨x, Finset.mem_coe.2 (Finset.mem_univ x), hx⟩) fun _ _ => rfl
end GeneralPieces.DefGenPieces

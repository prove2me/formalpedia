-- Prove2me | solution 1 for GeneralPieces.stFact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:50:27.554836+00:00
-- url     : https://prove2.me/submissions/9cee130a-2ff8-4b3a-a690-acd4b7f20032

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_Consts
import Definitions.Def_GeneralPieces_Half_Size
import Definitions.Def_GeneralPieces_Trim_Prog
import Definitions.Def_ClauseBound_Inst_HalfAll
import Definitions.Def_GeneralPieces_Half_Spec
import Theorems.Thm_ClauseBound_Boson_ApcL_col_eq
import Theorems.Thm_ClauseBound_Inst_Half_Fact_sum_words_eq
import Theorems.Thm_ClauseBound_Inst_Half_stEnc
import Theorems.Thm_ClauseBound_Inst_Half_stLabs
import Theorems.Thm_ClauseBound_Inst_Half_stVal_all
import Theorems.Thm_ClauseBound_Inst_Half_stWords
import Theorems.Thm_ClauseBound_Part_two_le_hOf
import Theorems.Thm_ClauseBound_Part_two_pow_le_p_hOf
import Theorems.Thm_GeneralPieces_ApcL_row_eq
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half Finset
namespace GeneralPieces
theorem _root_.solution (hPF : AppHalfPieces.PieceFacts) : StFact := by
  intro c₀ c lam pad hl hC hp h' i hi x y u v
  have hh : 1 ≤ ClauseBound.Part.hOf lam := le_trans (by norm_num) (ClauseBound.Part.two_le_hOf lam)
  have hℓ : ∀ x : Pieces.Bits lam, ClauseBound.Boson.Pos (ell (ClauseBound.Part.hOf lam) x) ∧ (ell (ClauseBound.Part.hOf lam) x).sum = ClauseBound.Part.hOf lam :=
    fun x => ⟨((stEnc lam _ hh (ClauseBound.Part.two_pow_le_p_hOf lam)).1 x).1, ((stEnc lam _ hh (ClauseBound.Part.two_pow_le_p_hOf lam)).1 x).2.1⟩
  constructor
  · rw [Fact.sum_words_eq stWords stLabs stVal_all hl hC hp false h' hi, ApcL_row_eq hPF hℓ hh]
    rfl
  · rw [Fact.sum_words_eq stWords stLabs stVal_all hl hC hp true h' hi, ClauseBound.Boson.ApcL_col_eq hℓ]
    rfl
end GeneralPieces

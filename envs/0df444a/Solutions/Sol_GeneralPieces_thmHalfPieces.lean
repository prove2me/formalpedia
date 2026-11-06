-- Prove2me | solution 1 for GeneralPieces.thmHalfPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:50:01.419371+00:00
-- url     : https://prove2.me/submissions/f760d961-8501-40db-bd44-7c54f5b34c2f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_Spec
import Definitions.Def_GeneralPieces_Half_Order
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Definitions.Def_ClauseBound_Inst_CertHalf
import Definitions.Def_ClauseBound_Inst_HalfEnd
import Definitions.Def_GeneralPieces_Half_Main
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_cnt
import Theorems.Thm_ClauseBound_Inst_Half_Cert_halfF_keeps
import Theorems.Thm_ClauseBound_Inst_Half_Fact_cap_eq
import Theorems.Thm_ClauseBound_Inst_Half_hF_eq
import Theorems.Thm_ClauseBound_Inst_Half_half_le
import Theorems.Thm_ClauseBound_Inst_Half_lt_one
import Theorems.Thm_ClauseBound_Inst_Half_stEnc
import Theorems.Thm_ClauseBound_Inst_Rec_factN_eq
import Theorems.Thm_ClauseBound_Part_two_le_hOf
import Theorems.Thm_ClauseBound_Part_two_pow_le_p_hOf
import Theorems.Thm_GeneralPieces_ApcL_eq_piece
import Theorems.Thm_GeneralPieces_Half_hOf_eq
import Theorems.Thm_GeneralPieces_Half_isMu
import Theorems.Thm_GeneralPieces_Lex_hOf_eq
import Theorems.Thm_GeneralPieces_exists_par_half2
import Theorems.Thm_GeneralPieces_half_realizes
import Theorems.Thm_GeneralPieces_of_par_realizes
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_PaddedDescent_F_cap_eq
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half GeneralPieces.Half
namespace GeneralPieces
theorem _root_.solution (hPF : AppHalfPieces.PieceFacts) : AppRunningTime.ThmHalfPieces := by
  obtain ⟨c₀, c, hP, hC⟩ := exists_par_half2 hPF
  refine ⟨max (c + 1) (2 * (halfF c₀ c).m), halfF c₀ c, halfA, valOf (halfF c₀ c),
    of_par_realizes hP (Cert.halfF_keeps c₀ c) half_le lt_one fun lam hl => half_realizes hPF 0 hl (hC lam hl), fun lam hl => ?_⟩
  have hhF : hF c₀ lam = ClauseBound.Part.hOf lam := hF_eq (hC lam hl).h_le
  have hh1 : 1 ≤ ClauseBound.Part.hOf lam := le_trans (by norm_num) (ClauseBound.Part.two_le_hOf lam)
  have hℓ : ∀ x : Pieces.Bits lam, ClauseBound.Boson.Pos (ell (ClauseBound.Part.hOf lam) x) ∧ (ell (ClauseBound.Part.hOf lam) x).sum = ClauseBound.Part.hOf lam :=
    fun x => ⟨((stEnc lam _ hh1 (ClauseBound.Part.two_pow_le_p_hOf lam)).1 x).1, ((stEnc lam _ hh1 (ClauseBound.Part.two_pow_le_p_hOf lam)).1 x).2.1⟩
  have hcnt : (halfF c₀ c).cnt 0 lam = 4 * ClauseBound.Part.hOf lam + 1 := by
    change 4 * hF c₀ lam + 1 = _
    rw [hhF]
  rw [hOf_eq lam]
  refine ⟨fun x => ptn (ell (ClauseBound.Part.hOf lam) x), isMu (ClauseBound.Part.two_pow_le_p_hOf lam), hcnt, ?_, fun i hi => ⟨fun x y u v => ?_, ?_, ?_⟩⟩
  · change factN (hF c₀ lam) = _
    rw [factN_eq, hhF]
  · exact ApcL_eq_piece hPF hℓ hh1 _ x y u v
  · exact Fact.cap_eq (hC lam hl) false 0 (hcnt ▸ hi)
  · exact Fact.cap_eq (hC lam hl) true 0 (hcnt ▸ hi)
end GeneralPieces

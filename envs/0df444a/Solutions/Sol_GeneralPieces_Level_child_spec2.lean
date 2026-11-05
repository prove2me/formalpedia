-- Prove2me | solution 1 for GeneralPieces.Level.child_spec2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:30:45.35751+00:00
-- url     : https://prove2.me/submissions/d1a93365-947a-4cab-815f-903b844e85f4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Level
import Definitions.Def_GeneralPieces_Rec_Level
import Theorems.Thm_GeneralPieces_Level_zetaOf_mem
import Theorems.Thm_GeneralPieces_Level_cases_ii
import Theorems.Thm_GeneralPieces_Level_Lof_le_lamNext
import Theorems.Thm_GeneralPieces_grouping_general
import Theorems.Thm_GeneralPieces_wfe_mono
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Level
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.Level Finset
namespace GeneralPieces.Level
theorem _root_.solution (P : PiecesF) (pad : U) (s : Step) (lam B : ℕ) (I : PInst) (y : ℕ) (hL : LevelOK2 P s lam) (hlam : I.1.length = lam)
    (hb : BudG P pad.length s lam) (hy : y < nPat P s lam) (hc : (s.thin && colSide P s lam y) = false) (g e : ℕ) (hg : g = s.p) (he : e = s.d)
    (N : Network (Fin g) (List Bool) (List Bool))
    (hN : (gridF P).toP.Presents (gctx pad s (!s.thin && colSide P s lam y) I y) N 0 0)
    (hS : N.Sized (P.m * (g * e ^ 2 * lam)) (e * B + e ^ 2 * P.bits s.h lam))
    (hU : N.U = totalG P s.p s.d (!s.thin && colSide P s lam y) s.h lam y)
    (hM : ∀ a b, a ≠ b → N.c a b ≤ e ^ 2 * (P.m * lam)) :
    ∃ J, childG P pad s I y = some J ∧ zval s.K J = N.value ∧ WFe s.K (lamNextG P s lam) (bNextG P s lam B) J := by
  subst hg he
  obtain ⟨J, h1, h2, h3⟩ := grouping_general _ (gridF P) _ s.K s.p (zetaOf s) N _ _ (lamNextG P s lam) pad hL.two_le hL.two_le_p (zetaOf_mem hL.D_ge).1
    (zetaOf_mem hL.D_ge).2 hN hS (cases_ii hL N hM) (Lof_le_lamNext hL N.U (hU ▸ hL.ubar y hy hc)) (Nat.le_add_left 1 _) hb.col hb.st hb.lab hb.tab
  refine ⟨J, ?_, h2, wfe_mono h3 (min_le_right _ _)⟩
  unfold childG
  rw [hlam]
  exact h1
end GeneralPieces.Level

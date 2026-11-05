-- Prove2me | solution 1 for GeneralPieces.Level.cases_ii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:23.028264+00:00
-- url     : https://prove2.me/submissions/7c1950a8-49e2-47c8-a8ab-bdd7df2b6473

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Level
import Definitions.Def_GeneralPieces_Rec_Level

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Level
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.Level Finset
namespace GeneralPieces.Level
theorem _root_.solution {P : PiecesF} {s : Step} {lam : ℕ} (hL : LevelOK2 P s lam) (N : Network (Fin s.p) (List Bool) (List Bool))
    (hM : ∀ a b, a ≠ b → N.c a b ≤ s.d ^ 2 * (P.m * lam)) : AppRunningTime.Cases s.K s.p (zetaOf s) (P.m * (s.p * s.d ^ 2 * lam)) N.c := by
  refine Or.inr ⟨hL.dvd, fun a b hab => ?_, hL.hoeffding⟩
  have hp : (0 : ℝ) < s.p := by exact_mod_cast (by have := hL.two_le_p; omega : 0 < s.p)
  rw [le_div_iff₀ hp]
  have h : N.c a b * s.p ≤ P.m * (s.p * s.d ^ 2 * lam) := by
    calc N.c a b * s.p ≤ s.d ^ 2 * (P.m * lam) * s.p := Nat.mul_le_mul_right _ (hM a b hab)
      _ = P.m * (s.p * s.d ^ 2 * lam) := by ring
  exact_mod_cast h
end GeneralPieces.Level

-- Prove2me | solution 1 for GeneralPieces.valF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:13:05.408979+00:00
-- url     : https://prove2.me/submissions/ad7835e8-8199-4781-8147-a9ba3474e6e6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_DefGenPieces_Progs
import Definitions.Def_GeneralPieces_Trim_Prog
import Theorems.Thm_GeneralPieces_Trim_valF_eq_sum
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen
open Trim
namespace GeneralPieces
theorem _root_.solution {P : PiecesF} {h lam : ℕ} {A : ℕ → Pieces.Four lam} (hA : Realizes P h lam A) {pad : U} (hn : 2 ^ P.need h lam ≤ pad.length) {i : ℕ}
    (hi : i < P.cnt h lam) (hc : ∀ tr, 2 ^ P.cap tr h lam i ≤ pad.length) (x y u v : Pieces.Bits lam) :
    valF P ((pad, false), (rep h, i), (bitsOf x, bitsOf y, bitsOf u, bitsOf v)) = A i x y u v ∧
      valF P ((pad, true), (rep h, i), (bitsOf x, bitsOf u, bitsOf y, bitsOf v)) = A i x y u v :=
  ⟨(valF_eq_sum P (hc false) x y u v).trans ((hA.2.2 pad hn i hi).1 x y u v).symm,
    (valF_eq_sum P (hc true) x u y v).trans ((hA.2.2 pad hn i hi).2.1 x y u v).symm⟩
end GeneralPieces

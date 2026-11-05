-- Prove2me | solution 1 for GeneralPieces.atZero_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:31.406191+00:00
-- url     : https://prove2.me/submissions/3c966b73-c019-45f6-88c6-92dd1d991556

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Trim_Cert
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Theorems.Thm_GeneralPieces_cnt_pos_of_isPieces
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Prog_NetE_cap_le
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
open DefGenPieces Trim
variable {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : ValQ → ℤ}
namespace GeneralPieces
theorem _root_.solution (h : IsPieces ρ c P A val) {m : ℕ} (hm : 1 ≤ m) (hcap : ∀ tr lam i, 1 ≤ lam → i < P.cnt 0 lam → P.cap tr 0 lam i ≤ 2 * m * lam)
    (hh : ℕ) {lam : ℕ} (hl : 1 ≤ lam) : (atZero P c m).Spec hh lam where
  cnt_pos := cnt_pos_of_isPieces h hl
  d_pos := h.d_pos lam hl
  m_pos := hm
  cap_le tr i hi := hcap tr lam i hl hi
  ex := ⟨A lam, h.sum lam hl, fun i hi x y u v => (h.size_A lam hl i hi x y u v).le, fun pad hp i hi =>
    ⟨h.row lam hl pad hp i hi, h.col lam hl pad hp i hi, fun tr x y θ => ⟨(h.size_f lam hl pad hp i hi tr x y θ).1.le, (h.size_f lam hl pad hp i hi tr x y θ).2.le⟩⟩⟩
end GeneralPieces

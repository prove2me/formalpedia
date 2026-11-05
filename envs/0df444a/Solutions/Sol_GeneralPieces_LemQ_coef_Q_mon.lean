-- Prove2me | solution 1 for GeneralPieces.LemQ.coef_Q_mon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:16:26.995742+00:00
-- url     : https://prove2.me/submissions/f16ae090-4c2a-4132-8304-c14ffeeea5ce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_coef_sum
import Theorems.Thm_GeneralPieces_LemQ_sum_lst
import Theorems.Thm_GeneralPieces_LemQ_angle_tpow
import Theorems.Thm_GeneralPieces_LemQ_coef_comp
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul
import Theorems.Thm_GeneralPieces_Ring_coef_smul


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (hB : StBridge) (hOp : OpFacts) (h1 : O1) {h : ℕ} {μ ν : Ptn} (hμ : wt μ ≤ h) (hν : wt ν = h) (s : ℤ) (π σ : Ptn) :
    coef π (Q h s (tpow μ) (tpow ν) (tpow σ)) = (ClauseBound.Boson.Qk [((1 : ℤ), lst μ)] (lst ν) s (toN π) (toN σ) : ℚ) := by
  unfold Q ClauseBound.Boson.Qk
  rw [coef_sum, sum_lst, hν]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [coef_smul, angle_tpow i hμ, hOp.smul_left, coef_smul, coef_comp hB hOp h1]
  simp [sum_lst]
end GeneralPieces.LemQ

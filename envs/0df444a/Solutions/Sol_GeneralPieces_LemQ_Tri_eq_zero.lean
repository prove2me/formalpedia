-- Prove2me | solution 1 for GeneralPieces.LemQ.Tri.eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:14:09.468442+00:00
-- url     : https://prove2.me/submissions/c903f1de-1a85-4cd2-bcf5-26d84612249d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_eq_sum_ptnsZ
import Theorems.Thm_GeneralPieces_LemQ_mem_ptnsLe
import Theorems.Thm_GeneralPieces_LemQ_eq_sum_ptnsLe
import Theorems.Thm_P2M_GeneralPieces_LemQ_Tri_sum__d29a426cc3fb
import Theorems.Thm_P2M_GeneralPieces_LemQ_Tri_sum__6d04f4d04421
import Theorems.Thm_P2M_GeneralPieces_LemQ_Tri_sum__2b3f9b0cd408
import Theorems.Thm_GeneralPieces_Ring_mem_ptnsZ


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.LemQ.Tri
variable {T T' : V → V → V → V}
namespace GeneralPieces.LemQ.Tri
theorem _root_.solution (hT : Tri T) {h E : ℕ} (hmon : ∀ μ ν σ : Ptn, wt μ ≤ h → wt ν = h → wt σ = E → T (tpow μ) (tpow ν) (tpow σ) = 0)
    {a b f : V} (ha : WtLe h a) (hb : b ∈ VE h) (hf : f ∈ VE E) : T a b f = 0 := by
  rw [eq_sum_ptnsLe ha, eq_sum_ptnsZ hb, eq_sum_ptnsZ hf, hT.sum₁]
  refine sum_eq_zero fun μ hμ => ?_
  rw [hT.sum₂, sum_eq_zero, smul_zero]
  intro ν hν
  rw [hT.sum₃, sum_eq_zero, smul_zero]
  intro σ hσ
  rw [hmon μ ν σ ((mem_ptnsLe h μ).1 hμ) (by exact_mod_cast (mem_ptnsZ _ ν).1 hν) (by exact_mod_cast (mem_ptnsZ _ σ).1 hσ), smul_zero]
end GeneralPieces.LemQ.Tri

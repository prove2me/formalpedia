-- Prove2me | solution 1 for GeneralPieces.Pcs.bFam_mem
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:05:06.795645+00:00
-- url     : https://prove2.me/submissions/500cd3a0-9ee4-4b68-8a1e-efade067d6dd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

private theorem weight_toFinsupp_aux (μ : Ptn) :
    Finsupp.weight wgt (Multiset.toFinsupp μ) = wt μ := by
  induction μ using Multiset.induction_on with
  | empty => simp [wt]
  | cons a s ih =>
    rw [← Multiset.singleton_add, map_add, map_add, ih, Multiset.toFinsupp_singleton,
      Finsupp.weight_single]
    simp [wt, wgt]

private theorem mem_VE_natCast_aux (E : ℕ) (f : V) :
    f ∈ VE (E : ℤ) ↔ IsWeightedHomogeneous wgt f E := by
  have hVE : VE (E : ℤ) = weightedHomogeneousSubmodule ℚ wgt E := by
    rw [VE, if_pos (by omega), Int.toNat_natCast]
    rfl
  rw [hVE, mem_weightedHomogeneousSubmodule]

private theorem tpow_mem_VE_aux (μ : Ptn) : tpow μ ∈ VE (wt μ : ℤ) := by
  rw [mem_VE_natCast_aux]
  exact isWeightedHomogeneous_monomial _ _ _ (weight_toFinsupp_aux μ)

theorem solution (ν : Ptn) : bFam ν ∈ VE (wt ν : ℤ) := by
  exact Submodule.smul_mem _ _ (tpow_mem_VE_aux ν)

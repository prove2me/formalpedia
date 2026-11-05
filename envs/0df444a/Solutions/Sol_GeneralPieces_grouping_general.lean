-- Prove2me | solution 1 for GeneralPieces.grouping_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:21:51.948019+00:00
-- url     : https://prove2.me/submissions/f953841d-fc0d-4211-a882-93e4b1b6c030

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Group_CaseI
import Definitions.Def_GeneralPieces_Group_CaseII
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_CertG
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_GeneralPieces_Group_Lemma
import Theorems.Thm_GeneralPieces_Group_exists_grouping_lt
import Theorems.Thm_P2M_GeneralPieces_Group_rebalG_spec__c4a38d127b08
import Theorems.Thm_GeneralPieces_Group_goodG_of_grouping
import Theorems.Thm_P2M_GeneralPieces_Group_le_B_of_b549728d8dae
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_RebalF_rebalG_spec
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork PaddedDescent.F ClauseBound.Alg GeneralPieces.Group
namespace GeneralPieces
theorem _root_.solution (C : Type) (F : FNet C) (x : C) (K g : ℕ) (ζ : ℝ) (N : Network (Fin g) (List Bool) (List Bool)) (P B β : ℕ) (pad : U)
    (hK : 2 ≤ K) (hg : 2 ≤ g) (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1) (hN : F.toP.Presents x N 0 0) (hS : N.Sized P B) (hcase : AppRunningTime.Cases K g ζ P N.c)
    (hβ : AppRunningTime.Lof K g ζ P N.U ≤ β) (hβ1 : 1 ≤ β) (f1 : K ^ g ≤ pad.length) (f2 : 2 ^ (P * (2 * g / K)) ≤ pad.length) (f3 : 2 ^ P ≤ pad.length)
    (f4 : 2 ^ ((K - 1) * β) ≤ pad.length) :
    ∃ J, rebalG pad K g β F x = some J ∧ zval K J = N.value ∧
      WFe K β (min (AppRunningTime.B'of K g P B) (P * (2 * g / K) + B * (2 * g / K + 2 * g / K * (2 * g / K)) * K)) J := by
  obtain ⟨χ, h1, h2⟩ := exists_grouping_lt K g ζ P N.c hK hg hζ0 hζ1 hS.c_symm hS.sum_c hcase
  have hex := goodG_of_grouping F.toP (by omega) hN χ h1 fun γ γ' hne => (h2 γ γ' hne).trans hβ
  obtain ⟨J, a1, a2, a3, a4⟩ := rebalG_spec' pad K g β F x N P B hK (by omega) hβ1 hN hS hex f1 f2 f3 f4
  obtain ⟨J', b1, -, -, b4⟩ := RebalF.rebalG_spec pad K g β F x N P B hK (by omega) hβ1 hN hS hex f1 f2 f3 f4
  obtain rfl : J = J' := Option.some.inj (a1.symm.trans b1)
  refine ⟨J, a1, a2, ⟨a4.lam_pos, a4.lam_le, a4.rows, a4.row_len, fun r hr z hz => ?_⟩, a3⟩
  rcases le_total (AppRunningTime.B'of K g P B) (P * (2 * g / K) + B * (2 * g / K + 2 * g / K * (2 * g / K)) * K) with h | h
  · rw [min_eq_left h]
    exact (a4.abs_le r hr z hz).trans (Nat.pow_le_pow_right (by norm_num) (le_B'of K g P B (by omega)))
  · rw [min_eq_right h]
    exact b4.abs_le r hr z hz
end GeneralPieces

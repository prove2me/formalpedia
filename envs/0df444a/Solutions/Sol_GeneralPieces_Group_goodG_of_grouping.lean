-- Prove2me | solution 1 for GeneralPieces.Group.goodG_of_grouping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:56.12682+00:00
-- url     : https://prove2.me/submissions/125640a6-ab6f-4ce5-8648-8b278fbe5aa2

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
import Theorems.Thm_Groundwork_Network_merge_c
import Theorems.Thm_PaddedDescent_Col_goodG_iff


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset Groundwork
variable {J J' σ τ A : Type*}
open Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F PaddedDescent.F.RebalF PaddedDescent.Col
namespace GeneralPieces.Group
theorem _root_.solution {C : Type} {K g β : ℕ} (Np : PNet C) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ} (hK : 0 < K)
    (hN : Np.Presents c N t S) (χ : Fin g → Fin K) (h1 : ∀ γ, K * #{a | χ a = γ} < 2 * g)
    (h2 : ∀ γ γ', γ ≠ γ' → ∑ a with χ a = γ, ∑ b with χ b = γ', N.c a b ≤ β) : ∃ x < K ^ g, goodG K g Np β (c, x) = true := by
  have hχ : chi hK (finFunctionFinEquiv χ).val = χ := by
    funext a
    have := congrFun (finFunctionFinEquiv.symm_apply_apply χ) a
    rw [← this]
    rfl
  refine ⟨(finFunctionFinEquiv χ).val, (finFunctionFinEquiv χ).2, (goodG_iff Np hK hN β _).2 ?_⟩
  rw [hχ]
  exact ⟨h1, fun G G' hne => by rw [Network.merge_c]; exact h2 G G' hne⟩
end GeneralPieces.Group

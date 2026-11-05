-- Prove2me | solution 1 for GeneralPieces.Group.display_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:34.90042+00:00
-- url     : https://prove2.me/submissions/f0e2e256-2b83-4f8e-b324-56c8ea684198

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
import Theorems.Thm_ClauseBound_Group_Grouping_card_cls
import Theorems.Thm_ClauseBound_Group_Grouping_disjoint_cls


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution (hn : 1 ≤ n) (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (e : Equiv.Perm (Fin (K * n)))
    (h2 : ∀ a γ', ∑ b ∈ cls e γ', cz c a b < (cs c a + ζ * P) / K) {γ γ' : Fin K} (hne : γ ≠ γ') :
    Yg c e γ γ' < 1 / K * ∑ a ∈ cls e γ, cs c a + ((K * n : ℕ) : ℝ) / K * (ζ * P / K) := by
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact γ.elim0
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hY : Yg c e γ γ' = ∑ a ∈ cls e γ, ∑ b ∈ cls e γ', cz c a b :=
    sum_congr rfl fun a ha => sum_congr rfl fun b hb =>
      (if_neg fun h : a = b => disjoint_left.1 (disjoint_cls e hne) ha (h ▸ hb)).symm
  have hne' : (cls e γ).Nonempty := card_pos.1 (by rw [card_cls]; exact hn)
  calc Yg c e γ γ' < ∑ a ∈ cls e γ, (cs c a + ζ * P) / K := by rw [hY]; exact sum_lt_sum_of_nonempty hne' fun a _ => h2 a γ'
    _ = 1 / K * ∑ a ∈ cls e γ, cs c a + ((K * n : ℕ) : ℝ) / K * (ζ * P / K) := by
        rw [← sum_div, sum_add_distrib, sum_const, card_cls, nsmul_eq_mul]
        push_cast
        field_simp
end GeneralPieces.Group

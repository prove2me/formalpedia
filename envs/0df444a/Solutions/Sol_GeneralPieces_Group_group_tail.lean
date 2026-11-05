-- Prove2me | solution 1 for GeneralPieces.Group.group_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:50:40.361243+00:00
-- url     : https://prove2.me/submissions/ff0792d6-407d-4b1b-8141-20ebe0b14fae

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
import Theorems.Thm_GeneralPieces_Group_group_uniform
import Theorems.Thm_GeneralPieces_Group_hoeffding_sample

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution (hK : 1 ≤ K) (hn : 1 ≤ n) (x : Fin (K * n) → ℝ) {R ζ : ℝ} (hR : 0 < R) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ R) (hζ : 0 ≤ ζ) (γ : Fin K) :
    (#{e : Equiv.Perm (Fin (K * n)) | (∑ i, x i) / K + ζ * n * R ≤ ∑ i ∈ cls e γ, x i} : ℝ) ≤
      Real.exp (-(2 * n * ζ ^ 2)) * #(univ : Finset (Equiv.Perm (Fin (K * n)))) := by
  have : Nonempty (Fin (K * n)) := ⟨⟨0, Nat.mul_pos hK hn⟩⟩
  refine group_uniform γ (fun A => (∑ i, x i) / K + ζ * n * R ≤ ∑ i ∈ A, x i) _ ?_
  have w := hoeffding_sample univ x hR (fun i _ => hx i) univ_nonempty n hζ
  have e : (n : ℝ) * ((∑ i, x i) / #(univ : Finset (Fin (K * n)))) = (∑ i, x i) / K := by
    have hK0 : (K : ℝ) ≠ 0 := by positivity
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [card_univ, Fintype.card_fin]
    push_cast
    field_simp
  rwa [e] at w
end GeneralPieces.Group

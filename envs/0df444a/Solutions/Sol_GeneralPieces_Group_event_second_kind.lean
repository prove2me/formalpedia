-- Prove2me | solution 1 for GeneralPieces.Group.event_second_kind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:56:54.792199+00:00
-- url     : https://prove2.me/submissions/3f06efa6-0d5c-4adc-9c5b-0cfc57115eb4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
import Theorems.Thm_GeneralPieces_Group_group_tail
import Theorems.Thm_GeneralPieces_Group_cz_nonneg

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution (hK : 1 ≤ K) (hn : 1 ≤ n) (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (hζ : 0 ≤ ζ) (hP0 : 0 < P)
    (hPg : ∀ a b, a ≠ b → (c a b : ℝ) ≤ P / ((K * n : ℕ) : ℝ)) (a : Fin (K * n)) (γ' : Fin K) :
    (#{e : Equiv.Perm (Fin (K * n)) | (cs c a + ζ * P) / K ≤ ∑ b ∈ cls e γ', cz c a b} : ℝ) ≤
      Real.exp (-(2 * n * ζ ^ 2)) * #(univ : Finset (Equiv.Perm (Fin (K * n)))) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hg0 : (0 : ℝ) < ((K * n : ℕ) : ℝ) := by push_cast; positivity
  have hR : 0 < P / ((K * n : ℕ) : ℝ) := div_pos hP0 hg0
  have w := group_tail hK hn (cz c a) hR (fun b => ⟨cz_nonneg c a b, by
    unfold cz; split_ifs with h
    · exact hR.le
    · exact hPg a b h⟩) hζ γ'
  have e : (cs c a + ζ * P) / K = (∑ b, cz c a b) / K + ζ * n * (P / ((K * n : ℕ) : ℝ)) := by
    rw [cs]; push_cast; field_simp
  rwa [e]
end GeneralPieces.Group

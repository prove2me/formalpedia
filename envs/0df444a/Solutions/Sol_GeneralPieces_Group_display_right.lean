-- Prove2me | solution 1 for GeneralPieces.Group.display_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:37.640283+00:00
-- url     : https://prove2.me/submissions/93fdff25-27eb-4797-8f7c-ca09c3759141

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (e : Equiv.Perm (Fin (K * n)))
    (h1 : ∀ γ, ∑ a ∈ cls e γ, cs c a < (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K) (γ : Fin K) :
    1 / K * ∑ a ∈ cls e γ, cs c a + ((K * n : ℕ) : ℝ) / K * (ζ * P / K) < (tot c + 2 * ζ * ((K * n : ℕ) : ℝ) * P) / (K : ℝ) ^ 2 := by
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact γ.elim0
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have h := mul_lt_mul_of_pos_left (h1 γ) (one_div_pos.2 hK0)
  have e1 : 1 / (K : ℝ) * ((tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K) + ((K * n : ℕ) : ℝ) / K * (ζ * P / K) =
      (tot c + 2 * ζ * ((K * n : ℕ) : ℝ) * P) / (K : ℝ) ^ 2 := by
    field_simp
    ring
  linarith
end GeneralPieces.Group

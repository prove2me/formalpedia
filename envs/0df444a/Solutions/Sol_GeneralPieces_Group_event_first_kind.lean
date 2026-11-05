-- Prove2me | solution 1 for GeneralPieces.Group.event_first_kind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:56:51.649+00:00
-- url     : https://prove2.me/submissions/dbb61fa2-a59e-49f2-b46f-327b11d2483a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
import Theorems.Thm_GeneralPieces_Group_group_tail
import Theorems.Thm_GeneralPieces_Group_cs_nonneg

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution (hK : 1 ≤ K) (hn : 1 ≤ n) (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (hζ : 0 ≤ ζ) (hP0 : 0 < P)
    (hP : ∀ a, cs c a ≤ P) (γ : Fin K) :
    (#{e : Equiv.Perm (Fin (K * n)) | (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K ≤ ∑ a ∈ cls e γ, cs c a} : ℝ) ≤
      Real.exp (-(2 * n * ζ ^ 2)) * #(univ : Finset (Equiv.Perm (Fin (K * n)))) := by
  have w := group_tail hK hn (cs c) hP0 (fun a => ⟨cs_nonneg c a, hP a⟩) hζ γ
  have e : (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K = (∑ a, cs c a) / K + ζ * n * P := by
    have hK0 : (K : ℝ) ≠ 0 := by positivity
    rw [tot]; push_cast; field_simp
  rwa [e]
end GeneralPieces.Group

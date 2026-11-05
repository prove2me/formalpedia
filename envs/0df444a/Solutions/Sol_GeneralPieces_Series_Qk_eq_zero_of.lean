-- Prove2me | solution 1 for GeneralPieces.Series.Qk_eq_zero_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:13:39.807208+00:00
-- url     : https://prove2.me/submissions/86368a7a-738d-4465-a106-d6980c96cd52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Constant
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_GeneralPieces_Series_LemmaQ
import Theorems.Thm_GeneralPieces_Series_Qk_eq_sum
import Theorems.Thm_GeneralPieces_Series_Expansion_qP_eq_zero


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {A : FA} {b : List ℕ}
namespace GeneralPieces.Series
theorem _root_.solution (h : StExpansion) (hA : A.Ok b.sum) (hb : Pos b) {s : ℤ} {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) (hs : (σ.sum : ℤ) + b.sum < |s|) :
    Qk A b s π σ = 0 := by
  rw [Qk_eq_sum hA]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  obtain ⟨G, hG⟩ := h c.2 b (hA c hc).1 hb
  obtain ⟨X⟩ := hG π σ hπ hσ
  rw [X.qP_eq_zero (hA c hc).2 hs, mul_zero]
end GeneralPieces.Series

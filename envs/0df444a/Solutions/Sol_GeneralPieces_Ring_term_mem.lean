-- Prove2me | solution 1 for GeneralPieces.Ring.term_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:39:59.905345+00:00
-- url     : https://prove2.me/submissions/f430a08f-94e3-4623-bfa3-4e3467b7f180

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_foldr_nabla_mem
import Theorems.Thm_GeneralPieces_Ring_filter_sums
import Theorems.Thm_GeneralPieces_Ring_term_eq


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : List ℕ+) (ks : List ℤ) {E : ℤ} {f : V} (hf : f ∈ VE E) : term μ ks f ∈ VE (E - ks.sum) := by
  obtain ⟨-, -, a3, -⟩ := filter_sums ks
  rw [term_eq]
  refine Submodule.smul_mem _ _ ?_
  have h1 := foldr_nabla_mem (ks.filter (0 < ·)) (fun k hk => (by simpa using (List.mem_filter.1 hk).2 : 0 < k).ne') hf
  have h2 := foldr_nabla_mem (ks.filter (· < 0)) (fun k hk => (by simpa using (List.mem_filter.1 hk).2 : k < 0).ne) h1
  rwa [show E - (ks.filter (0 < ·)).sum - (ks.filter (· < 0)).sum = E - ks.sum by rw [a3]; ring] at h2
end GeneralPieces.Ring

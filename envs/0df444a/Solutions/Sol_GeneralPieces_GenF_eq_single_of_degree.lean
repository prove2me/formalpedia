-- Prove2me | solution 1 for GeneralPieces.GenF.eq_single_of_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:48:22.441261+00:00
-- url     : https://prove2.me/submissions/c2ab0a86-0fe9-4cbf-8546-4396fb90cb5f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution {Y : Type} {m : Y →₀ ℕ} (h : m.degree = 1) : ∃ l, m = Finsupp.single l 1 := by
  have hm : m ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact absurd h (by norm_num)
  obtain ⟨l, hl⟩ := Finsupp.support_nonempty_iff.2 hm
  have h1 := degree_sub_single hl
  have h2 : m - Finsupp.single l 1 = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
  refine ⟨l, ?_⟩
  have h3 := sub_single_add hl
  rw [h2, zero_add] at h3
  exact h3.symm
end GeneralPieces.GenF

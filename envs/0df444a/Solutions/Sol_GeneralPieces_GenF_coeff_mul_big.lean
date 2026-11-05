-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_mul_big
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:36:17.347185+00:00
-- url     : https://prove2.me/submissions/94207973-ad1c-4531-a204-0bd758db557e

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
theorem _root_.solution {R : Type} [CommRing R] (f g : HahnSeries ℤ R) {A B : Set ℤ} (hA : A.IsPWO) (hB : B.IsPWO) (hf : f.support ⊆ A) (hg : g.support ⊆ B) (y : ℤ) :
    (f * g).coeff y = ∑ ij ∈ Finset.antidiagonal hA hB y, f.coeff ij.1 * g.coeff ij.2 := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_subset (fun ij h => ?_) fun ij h hn => ?_
  · rw [Finset.mem_antidiagonal] at h ⊢
    exact ⟨hf h.1, hg h.2.1, h.2.2⟩
  · by_contra hne
    refine hn ?_
    rw [Finset.mem_antidiagonal]
    exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne, (Finset.mem_antidiagonal.1 h).2.2⟩
end GeneralPieces.GenF

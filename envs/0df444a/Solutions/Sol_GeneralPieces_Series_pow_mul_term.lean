-- Prove2me | solution 1 for GeneralPieces.Series.pow_mul_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:06:09.526445+00:00
-- url     : https://prove2.me/submissions/46732746-360f-40c9-a446-10000af597d7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Expansion
import Definitions.Def_GeneralPieces_Series_OneLaurent

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
namespace GeneralPieces.Series
theorem _root_.solution {A : Type} [CommRing A] [Algebra ℚ A] {d e : A} (h : d * e = 1) {N H : ℕ} (hN : N ≤ H) (r : ℚ) (n : A) :
    d ^ H * (r • (e ^ N * n)) = r • (d ^ (H - N) * n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left, mul_smul_comm, pow_add, show d ^ N * d ^ k * (e ^ N * n) = (d * e) ^ N * (d ^ k * n) by rw [mul_pow]; ring, h, one_pow, one_mul]
end GeneralPieces.Series

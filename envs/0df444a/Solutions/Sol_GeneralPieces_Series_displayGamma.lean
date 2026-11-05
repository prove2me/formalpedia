-- Prove2me | solution 1 for GeneralPieces.Series.displayGamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:36:07.573524+00:00
-- url     : https://prove2.me/submissions/bfe51342-1aeb-4192-840d-37dc3d550a27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_iter_smul
import Theorems.Thm_GeneralPieces_Series_iter_pos
import Theorems.Thm_GeneralPieces_Series_iter_neg

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
variable {A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.Series
theorem _root_.solution (D₁ D₂ : Derivation ℚ A A) {ε : A} (h₁ : D₁ ε = -ε ^ 2) (h₂ : D₂ ε = ε ^ 2) {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (1 / (((j - 1).factorial : ℚ) * ((n - 1).factorial : ℚ))) • D₁^[j - 1] (D₂^[n - 1] (ε ^ 2)) = (ClauseBound.Boson.Gam j n : ℚ) • ε ^ (j + n) := by
  obtain ⟨a, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  have e := iter_pos D₂ h₂ b 1
  rw [Nat.factorial_one, Nat.cast_one, one_smul] at e
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel, e, iter_smul, iter_neg D₁ h₁, smul_smul, smul_smul,
    show 1 + 1 + b + a = a + 1 + (b + 1) by omega]
  congr 1
  have ha : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hb : (b.factorial : ℚ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  rw [ClauseBound.Boson.Gam, Nat.add_sub_cancel, show 1 + b = b + 1 by omega, Nat.factorial_succ]
  push_cast
  rw [show (-(2 + (b : ℤ))) = -((b : ℤ) + 1) - 1 by ring]
  field_simp
end GeneralPieces.Series

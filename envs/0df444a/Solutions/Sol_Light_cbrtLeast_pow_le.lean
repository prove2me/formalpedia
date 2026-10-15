-- Prove2me | solution 1 for Light.cbrtLeast_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:35:50.782877+00:00
-- url     : https://prove2.me/submissions/0665cf33-16c1-497d-9dda-6222cd56a506

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light.Logs
end Light.Logs

section


/-!
# Logarithms, the cube root and halves, without division

Four routines on local variables only; none of them touches the memory.

* log2(x) returns ⌊log₂ x⌋ (0 for x = 0) by doubling (`log2_meets`).
* clog2(x) returns ⌈log₂ x⌉ (0 for x ≤ 1) by doubling (`clog2_meets`).
* cbrtCeil(n) returns the least s with s³ ≥ n, which is ⌈n^{1/3}⌉, by counting up
  (`cbrtCeil_meets`).
* half(h) returns ⌈h/2⌉ by counting up (`half_meets`).

Each of them is one loop that tries the candidates 0, 1, 2, … in turn.  Local variable 0 holds the
argument and receives the result, local variable 1 holds the candidate (`Arg`, `Cand`), and the two
logarithms keep a power of two in local variable 2 (`Power`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Logs







end Logs

open Logs

/-! ## The logarithm, rounded down -/















































/-! ## The logarithm, rounded up -/










































/-! ## The cube root, rounded up -/









theorem pow_lt_of_lt_cbrtLeast {n s : ℕ} (h : s < cbrtLeast n) : s ^ 3 < n :=
  not_le.1 (Nat.find_min (exists_le_cube n) h)














/-- The cube of the rounded cube root is at most 8 n. -/
theorem cbrtLeast_pow_le_sourceProof (n : ℕ) : cbrtLeast n ^ 3 ≤ 8 * n := by
  rcases Nat.eq_zero_or_pos (cbrtLeast n) with h | h
  · simp [h]
  obtain ⟨s, hs⟩ : ∃ s, cbrtLeast n = s + 1 := ⟨cbrtLeast n - 1, by omega⟩
  have h1 : s ^ 3 < n := pow_lt_of_lt_cbrtLeast (by omega)
  rw [hs]
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · subst h0
    omega
  · calc (s + 1) ^ 3 ≤ (2 * s) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * s ^ 3 := by ring
      _ ≤ 8 * n := by omega





























































/-! ## Halves, rounded up -/

































end Light

end
end


theorem solution : ∀ (n : Nat),
  @LE.le.{0} Nat instLENat
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Light.cbrtLeast n)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) n) := by
  exact @Light.cbrtLeast_pow_le_sourceProof

#print axioms solution

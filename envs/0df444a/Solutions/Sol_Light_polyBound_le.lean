-- Prove2me | solution 1 for Light.polyBound_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:03:59.455742+00:00
-- url     : https://prove2.me/submissions/710588c1-59de-4f47-abf4-7e73e91dde4c

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# A polynomial bound in the parameters fits in a word

The running-time claims hold at every word size W ≥ b (log₂ p₁ + ⋯ + log₂ p_r + 1), where p₁, …, p_r
are the parameters of the instance and the slope b is chosen with the program (`Admissible`).  A
light program states its limits as a polynomial in the parameters,
`polyBound s k params` = 2^s ((p₁ + 1) ⋯ (p_r + 1))^k.

The main fact is `polyBound_le`: this bound is at most 2^W as soon as b ≥ s + k r + k.  Each factor
p + 1 is at most 2^(log₂ p + 1) (`prod_succ_le`), so with S the sum of the logarithms the bound is
at most 2^(s + k (S + r)), and s + k (S + r) ≤ (s + k r + k) (S + 1) ≤ W.
-/

@[expose] public section

namespace Light

open ThreeSumApsp.WordRam




private theorem prod_succ_le (params : List ℕ) :
    (params.map (· + 1)).prod ≤ 2 ^ ((params.map Nat.log2).sum + params.length) := by
  induction params with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons]
    calc (p + 1) * (ps.map (· + 1)).prod
        ≤ 2 ^ (p.log2 + 1) * 2 ^ ((ps.map Nat.log2).sum + ps.length) :=
          Nat.mul_le_mul Nat.lt_log2_self ih
      _ = 2 ^ (p.log2 + (ps.map Nat.log2).sum + (ps.length + 1)) := by
          rw [← pow_add]
          congr 1
          omega

/-- At an admissible word size, words have room for a polynomial bound in the parameters, if the
slope is large enough. -/
theorem polyBound_le_sourceProof {b W s k r : ℕ} {params : List ℕ} (h : Admissible b params W)
    (hr : params.length ≤ r) (hb : s + k * r + k ≤ b) : polyBound s k params ≤ 2 ^ W := by
  set S := (params.map Nat.log2).sum
  have hexp : s + (S + params.length) * k ≤ W :=
    calc s + (S + params.length) * k ≤ s + (S + r) * k := by gcongr
      -- the difference is s S + k r S + k
      _ ≤ (s + k * r + k) * (S + 1) := Nat.le.intro (k := s * S + k * r * S + k) (by ring)
      _ ≤ b * (S + 1) := Nat.mul_le_mul_right _ hb
      _ ≤ W := h
  calc polyBound s k params ≤ 2 ^ s * (2 ^ (S + params.length)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (prod_succ_le params) k)
    _ = 2 ^ (s + (S + params.length) * k) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hexp





















































end Light

end


theorem solution : ∀ {b W s k r : Nat} {params : List.{0} Nat},
  ThreeSumApsp.WordRam.Admissible b params W →
    @LE.le.{0} Nat instLENat (@List.length.{0} Nat params) r →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) s
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k r))
            k)
          b →
        @LE.le.{0} Nat instLENat (Light.polyBound s k params)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W) := by
  exact @Light.polyBound_le_sourceProof

#print axioms solution

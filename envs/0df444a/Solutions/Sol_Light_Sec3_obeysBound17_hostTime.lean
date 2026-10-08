-- Prove2me | solution 1 for Light.Sec3.obeysBound17_hostTime
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T09:21:10.38124+00:00
-- url     : https://prove2.me/submissions/16489264-a279-44db-bee2-4be2fbd0f144

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Common
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec

section


/-!
# Ceilings of quotients and logarithms, floors and ceilings of roots

General facts about natural and real numbers. The quotient of two natural numbers, rounded up, is
Mathlib's `a ⌈/⌉ b`. It is computed by `Nat.ceilDiv_eq_add_pred_div : a ⌈/⌉ b = (a + b - 1) / b`.
It is the ceiling of the real quotient (`Nat.ceil_div_eq_ceilDiv`) and the least `k` with
`a ≤ k * b` (`Nat.ceilDiv_le_iff`, `Nat.lt_ceilDiv_iff`), so `a ≤ a ⌈/⌉ b * b < a + b`
(`Nat.le_ceilDiv_mul`, `Nat.ceilDiv_mul_lt`). The power of `b` with exponent `⌈log_b n⌉` is at most
`b * n` (`Nat.pow_clog_le_mul`). A natural number is compared with an `e`-th root by its `e`-th
power (`Real.natCast_le_rpow_inv_iff`, `Real.rpow_inv_le_natCast_iff`). `cbrtCeil n` is the cube
root of `n`, rounded up.
-/

public section

namespace Nat

/-! ## The ceiling of a quotient of natural numbers -/

/-- `a ⌈/⌉ b ≤ k` says that `k` pieces of size `b` cover `a`. Mathlib's `ceilDiv_le_iff_le_mul` has
`b * k` on the right. -/
theorem ceilDiv_le_iff {a b k : ℕ} (hb : 0 < b) : a ⌈/⌉ b ≤ k ↔ a ≤ k * b := by
  rw [ceilDiv_le_iff_le_mul hb, Nat.mul_comm]

/-- `i < a ⌈/⌉ b` says that `i` pieces of size `b` do not cover `a`. -/
theorem lt_ceilDiv_iff {a b i : ℕ} (hb : 0 < b) : i < a ⌈/⌉ b ↔ i * b < a := by
  rw [← Nat.not_le, ceilDiv_le_iff hb, Nat.not_le]





/-- `a ⌈/⌉ b` pieces of size `b` overshoot `a` by less than one piece. -/
theorem ceilDiv_mul_lt {a b : ℕ} (hb : 0 < b) : a ⌈/⌉ b * b < a + b := by
  have := Nat.div_mul_le_self (a + b - 1) b
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega











/-! ## The ceiling of a logarithm

`Real.natCeil_logb_natCast : ⌈Real.logb b n⌉₊ = Nat.clog b n` passes from real to natural numbers,
and `Nat.le_pow_clog : 1 < b → x ≤ b ^ Nat.clog b x` is the lower bound. -/

/-- Rounding `n ≥ 1` up to a power of `b` costs at most a factor `b`. -/
theorem pow_clog_le_mul {b n : ℕ} (hb : 1 < b) (hn : 1 ≤ n) : b ^ Nat.clog b n ≤ b * n := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn
  · simp [Nat.clog_one_right, hb.le]
  · have hpos : 0 < Nat.clog b n := Nat.clog_pos hb hn
    have hlt := Nat.pow_pred_clog_lt_self hb hn
    calc b ^ Nat.clog b n = b * b ^ (Nat.clog b n).pred := by
          rw [← Nat.pow_succ', Nat.succ_pred_eq_of_pos hpos]
      _ ≤ b * n := Nat.mul_le_mul_left b hlt.le

end Nat

namespace Real

/-! ## Roots

The `e`-th root of `t` is written `(t : ℝ) ^ ((e : ℝ)⁻¹)`. With these two lemmas,
`Nat.le_floor_iff` and `Nat.ceil_le`, its floor and its ceiling are described by powers of natural
numbers. -/















end Real

namespace ThreeSumApsp




end ThreeSumApsp

end
end

section


/-!
# Logarithms and real powers

Small facts on `Real.log`, `Real.logb`, `Nat.clog`, `Real.sqrt` and real powers that the estimates
of the paper use silently.

* Values, in the namespace `Real` and named by Mathlib's convention: `1 / 2 < log 2 < 1`,
  `log 4 = 2 log 2`, `log 9 = 2 log 3`, `1 ≤ log 4`, `1 / 2 ≤ log x` for `x ≥ 2`, `1 ≤ log x` for
  `x ≥ 3`, `log₂ 7 < 2.81`, `4 ≤ √D` for `D ≥ 16`.
* The rounded logarithm: `⌈log_b n⌉ < log_b n + 1` (`Real.natCast_clog_lt_logb_add_one`),
  `c ^ ⌈log_b n⌉ ≤ c * n ^ (log_b c)` (`Real.pow_clog_le_mul_rpow_logb`).
* The definition `logU u = log (max u 2)`, the paper's `log U`.
-/

@[expose] public section

namespace Real

/-! ### Values -/

/-- `1 / 2 < log 2`. -/
theorem one_half_lt_log_two : 1 / 2 < log 2 :=
  lt_trans (by norm_num) log_two_gt_d9










































/-! ### The rounded logarithm `Nat.clog` -/

/-- `⌈log_b n⌉ < log_b n + 1`, for all natural numbers `b` and `n` (for `b ≤ 1` or `n = 0` both
logarithms are `0`). -/
theorem natCast_clog_lt_logb_add_one (b n : ℕ) : (Nat.clog b n : ℝ) < logb b n + 1 := by
  rw [← natCeil_logb_natCast]
  exact Nat.ceil_lt_add_one (div_nonneg (log_natCast_nonneg n) (log_natCast_nonneg b))

/-- `c ^ ⌈log_b n⌉ ≤ c * n ^ (log_b c)`, for natural numbers `b` and `n ≥ 1` and a real number
`c ≥ 1`. -/
theorem pow_clog_le_mul_rpow_logb (b : ℕ) {n : ℕ} {c : ℝ} (hn : 1 ≤ n) (hc : 1 ≤ c) :
    c ^ Nat.clog b n ≤ c * (n : ℝ) ^ logb b c := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hswap : c ^ logb b n = (n : ℝ) ^ logb b c := by
    rw [rpow_def_of_pos hc0, rpow_def_of_pos (Nat.cast_pos.2 hn), logb, logb]
    ring_nf
  calc c ^ Nat.clog b n = c ^ (Nat.clog b n : ℝ) := (rpow_natCast c _).symm
    _ ≤ c ^ (logb b n + 1) :=
        rpow_le_rpow_of_exponent_le hc (natCast_clog_lt_logb_add_one b n).le
    _ = c * (n : ℝ) ^ logb b c := by rw [rpow_add_one hc0.ne', hswap, mul_comm]

end Real

namespace ThreeSumApsp






end ThreeSumApsp

end
end

section


/-!
# Bounds up to a constant factor, in several parameters

The paper writes `f = O(g)` for functions of several parameters that are tied by side conditions,
such as `D ^ 18 ≤ n` for the parameters `n`, `D`, `w`. `Dominated dom f g` says this: there is a
constant `C ≥ 0` with `f x ≤ C * g x` for every tuple `x` of parameters that satisfies `dom x`. If
there is no side condition, `dom` is `fun _ => True`. The type `α` of the parameters is best a
structure with one named field for each of them, so that a bound reads
`Dominated (fun p => p.D ^ 18 ≤ p.n) (fun p => cost p) fun p => p.n ^ 2 / p.D`.

The lemmas of this file are the steps that the paper takes without comment: such bounds can be
chained (`Dominated.trans`), added (`Dominated.add`, `Dominated.add_add`), multiplied and divided
(`Dominated.mul`, `Dominated.mul_left`, `Dominated.const_mul`, `Dominated.pow`,
`Dominated.div_right`), joined by a case distinction (`Dominated.ite`), restricted to a smaller
domain (`Dominated.mono_dom`) and specialized (`Dominated.comp`). With them no proof has to name a
constant. A bound enters the calculus by `Dominated.of_le`, `Dominated.of_le_const_mul` or
`Dominated.of_exists_const`, and leaves it by `obtain ⟨C, hC, hle⟩` or `Dominated.exists_const_and`.
For functions of one natural number, `Dominated.of_eventually` takes a bound for all large `n`,
`Dominated.isBigO` gives Mathlib's `f =O[atTop] g`, and `isBigO_comp_add_one` substitutes a size
that need not tend to infinity.

In every closure lemma the bound comes first and the side conditions follow.

For nonnegative `f` and `g` the notion is Mathlib's `f =O[𝓟 {x | dom x}] g`, big-O along the
principal filter of the domain (`dominated_iff_isBigO_principal`). The one-sided form is taken
because a running time is bounded from above only.

## The notions of "bounded up to a constant" in this library

* `f =O[atTop] g` of Mathlib bounds `|f|` for large `n`. In this sense `IsBigOPow f a` is `O(n^a)`,
  `IsPowPolylog f a` is `O(n^a (log n)^e)` for some `e`, and `IsPowLittleO f a` is `n^{a+o(1)}`.
  The exponents of the theorems are stated with them.
* `UpperBigOPow`, `UpperPowPolylog` and `UpperPowLittleO` are the same three classes as bounds on
  `f` and not on `|f|`, for running times. A two-sided bound gives the one-sided one
  (`IsBigOPow.upperBigOPow`, `IsPowPolylog.upperPowPolylog`, `IsPowLittleO.upperPowLittleO`).
* `Dominated dom f g` bounds `f` on the whole domain, for several parameters. It comes from a bound
  for large `n` by `Dominated.of_eventually` and gives one by `Dominated.isBigO`.
* `Scale.SoftO t e` says that a count `t` with values in `ℕ` is `Dominated` by a monomial with the
  exponents `e`, up to powers of one more quantity; the tactic `growth` reads the exponents off an
  explicit expression. It gives a `Dominated` bound by `Scale.SoftO.dominated`. Its instance
  `SoftOSqrtPow` gives `IsPowPolylog` by `SoftOSqrtPow.isPowPolylog`.
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp






namespace Dominated

variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

/-! ### Entering the calculus -/

/-- A bound with an explicit nonnegative constant. -/
theorem of_le_const_mul {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ x, dom x → f x ≤ C * g x) :
    Dominated dom f g :=
  ⟨C, hC, hfg⟩

/-- A bound with constant one. -/
theorem of_le (hfg : ∀ x, dom x → f x ≤ g x) : Dominated dom f g :=
  ⟨1, zero_le_one, fun x hx => by simpa only [one_mul] using hfg x hx⟩

/-- Every function is bounded by itself. -/
protected theorem refl (dom : α → Prop) (f : α → ℝ) : Dominated dom f f :=
  of_le fun _ _ => le_rfl


















/-- A constant is `O(g)` when `g ≥ 1` on the domain. -/
protected theorem const (c : ℝ) (hg : ∀ x, dom x → 1 ≤ g x) : Dominated dom (fun _ => c) g :=
  ⟨|c|, abs_nonneg c, fun x hx =>
    (le_abs_self c).trans (le_mul_of_one_le_right (abs_nonneg c) (hg x hx))⟩

/-! ### Leaving the calculus -/











/-! ### Chaining, restricting, substituting -/

/-- `f = O(g)` and `g = O(h)` give `f = O(h)`. -/
protected theorem trans (hfg : Dominated dom f g) (hgh : Dominated dom g h) :
    Dominated dom f h := by
  obtain ⟨C, hC, hf⟩ := hfg
  obtain ⟨D, hD, hg⟩ := hgh
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => (hf x hx).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hg x hx) hC






/-- The left side may be replaced by a smaller function. -/
theorem mono_left (hfg : Dominated dom f g) (hle : ∀ x, dom x → f' x ≤ f x) : Dominated dom f' g :=
  (of_le hle).trans hfg

/-- The right side may be replaced by a larger function. -/
theorem mono_right (hfg : Dominated dom f g) (hle : ∀ x, dom x → g x ≤ g' x) : Dominated dom f g' :=
  hfg.trans (of_le hle)

/-- Both sides may be replaced by functions that agree with them on the domain. -/
protected theorem congr (hfg : Dominated dom f g) (hf : ∀ x, dom x → f x = f' x)
    (hg : ∀ x, dom x → g x = g' x) : Dominated dom f' g' :=
  (hfg.mono_left fun x hx => (hf x hx).ge).mono_right fun x hx => (hg x hx).le








/-! ### Sums and case distinctions -/

/-- `O(h) + O(h) = O(h)`. -/
protected theorem add (hf : Dominated dom f h) (hg : Dominated dom g h) :
    Dominated dom (fun x => f x + g x) h := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, add_nonneg hC hD, fun x hx => ?_⟩
  rw [add_mul]
  exact add_le_add (hf x hx) (hg x hx)






















/-! ### Products and quotients -/

/-- A nonnegative constant factor on the left side is absorbed. -/
theorem const_mul (hfg : Dominated dom f g) {c : ℝ} (hc : 0 ≤ c) :
    Dominated dom (fun x => c * f x) g := by
  obtain ⟨C, hC, hf⟩ := hfg
  refine ⟨c * C, mul_nonneg hc hC, fun x hx => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x hx) hc






























/-- `O(g₁) · O(g₂) = O(g₁ g₂)` for nonnegative `f₁`, `f₂`. -/
protected theorem mul (h₁ : Dominated dom f₁ g₁) (h₂ : Dominated dom f₂ g₂)
    (hf₁ : ∀ x, dom x → 0 ≤ f₁ x) (hf₂ : ∀ x, dom x → 0 ≤ f₂ x) :
    Dominated dom (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x := by
  obtain ⟨C, hC, h₁⟩ := h₁
  obtain ⟨D, hD, h₂⟩ := h₂
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => ?_⟩
  rw [mul_mul_mul_comm]
  exact mul_le_mul (h₁ x hx) (h₂ x hx) (hf₂ x hx) ((hf₁ x hx).trans (h₁ x hx))

/-- `O(g) ^ e = O(g ^ e)` for nonnegative `f`. -/
protected theorem pow (hfg : Dominated dom f g) (hf : ∀ x, dom x → 0 ≤ f x) (e : ℕ) :
    Dominated dom (fun x => f x ^ e) fun x => g x ^ e := by
  obtain ⟨C, hC, hle⟩ := hfg
  refine ⟨C ^ e, pow_nonneg hC e, fun x hx => ?_⟩
  rw [← mul_pow]
  exact pow_le_pow_left₀ (hf x hx) (hle x hx) e

/-! ### Functions of one natural number -/








































end Dominated












end ThreeSumApsp

end
end

section


/-!
# Theorem 17, first step: hashing modulo a prime

The first step of the proof of Theorem 17 reduces the weights modulo a prime `p` in the range
`[√D/2, √D)` with few false positives.

* **Counting.**  The number of triples with `S(a,b,c) ≡ 0 (mod p)` is `F(p) + Z₀`
  (`TriangleInstance.countZeroMod_eq`), and it can be read off the product of two matrices over
  `ℤ[x]/(x^p − 1)` (`TriangleInstance.coeff_matP_mul_matQ`,
  `TriangleInstance.F_add_Z₀_eq_sum_coeff`).  There are fewer than `√D` primes in the range
  (`card_primesInRange_lt`).
* **Selecting.**  The prime with the smallest count exists
  (`TriangleInstance.exists_isSelectedPrime`) and has the fewest false positives
  (`TriangleInstance.IsSelectedPrime.F_le`).
* **The bound on `F(p)`**, `TriangleInstance.F_le_of_le_card_primesInRange` and
  `TriangleInstance.exists_F_le`.  A triple is a false positive of at most `log_{√D/2}(3n^ν)` primes
  in the range (`TriangleInstance.card_falsePositive_primes_le`), so the numbers `F(q)` add up to at
  most `n³` times that (`TriangleInstance.sum_F_le`); there are `Ω(√D/log D)` primes in the range
  (`exists_le_card_primesInRange`); `F(p)` is at most the average
  (`TriangleInstance.IsSelectedPrime.F_mul_card_le_sum`); and `log D ≤ 4 log(√D/2)`
  (`log_le_four_mul_log_sqrt_div_two`).  The constant of the bound has a name,
  `Hashing.falsePositiveConst`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ### The primes in the range -/












/-! ### The ring `ℤ[x]/(x^p − 1)` -/






namespace CyclicRing

open Polynomial

variable {p : ℕ}


































end CyclicRing












/-! ### Counting the triples with `S(a,b,c) ≡ 0 (mod p)` -/

namespace TriangleInstance

variable {n : ℕ} (T : TriangleInstance ℤ n)





















































































end TriangleInstance


















/-! ### Selecting the prime -/

namespace TriangleInstance

variable {n D p : ℕ} {κ : ℝ} (T : TriangleInstance ℤ n)
















/-! ### The bound on the number of false positives of the selected prime -/
















































































end TriangleInstance

































































































/-- The constant is at least 1. -/
theorem Hashing.one_le_falsePositiveConst : 1 ≤ Hashing.falsePositiveConst :=
  (Classical.choose_spec TriangleInstance.exists_F_le).1









end ThreeSumApsp

end
end

section


/-!
# Strassen's algorithm on lists, and the count of the proof of Theorem 17

Proof of Theorem 17: "Computing PQ takes […] O(n^{log₂ 7}) with Strassen's algorithm".
`strassenList` multiplies two `2^K × 2^K` matrices over `ℤ[x]/(x^p - 1)`, given as lists in Z-order,
and `countOf` reads the number of triples `(a,b,c)` with `S(a,b,c) = w(a,b) + w(b,c) + w(a,c) ≡ 0
(mod p)` off the product.

1. `zRing hp K α` is the list of the matrix `α` over the ring.  The operations on lists are the
   operations of the ring, entry by entry (`zRing_add`, `zRing_sub`), and the quadrants of a matrix
   are the quarters of its list (`quarter_zRing`, `zRing_succ`).
2. `strassenList_zRing`: the algorithm computes the product.  By induction on `K`; Strassen's seven
   products give the four quadrants of the product by an identity that holds summand by summand.
   It makes `7^K` multiplications in the ring, which is `O(n^{log₂ 7})` (`seven_pow_clog_le`).
3. The lists that the routine fills are the matrices `P` and `Q` of the proof of Theorem 17, padded
   with zeros to `2^K` rows and columns (`matPList_eq_zRing`, `matQList_eq_zRing`), and the padding
   does not change the entries of the product (`sum_padP_mul_padQ`).
4. `countOf_eq`: the count is the count of the proof of Theorem 17.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

open Finset

/-! ## Matrices over the ring, as lists -/

section Ring

variable {p : ℕ} (hp : p ≠ 0) (K : ℕ)
































end Ring

/-! ## Strassen's algorithm -/

















































/-- `strassenList p K` calls `cconv` seven times per level, `7^K` times in all.  For `K = ⌈log₂ n⌉`
this is the `O(n^{log₂ 7})` of the proof of Theorem 17: `7^{⌈log₂ n⌉} ≤ 7 n^{log₂ 7}`. -/
theorem seven_pow_clog_le {n : ℕ} (hn : 1 ≤ n) :
    (7 : ℝ) ^ Nat.clog 2 n ≤ 7 * (n : ℝ) ^ Real.logb 2 7 := by
  simpa using Real.pow_clog_le_mul_rpow_logb 2 hn (c := 7) (by norm_num)

/-! ## The count of the proof of Theorem 17 -/


























section Count

variable {n : ℕ} (T : TriangleInstance ℤ n) {p : ℕ}


















variable (n) (AB BC AC : List ℤ)











































end Count

end ThreeSumApsp.Spec

end
end

section


/-!
# The parameters of Theorems 17 and 19 in integer arithmetic

The proof of Theorem 19 chooses `D` and `g` as rounded real powers of `n`: "Let D be the largest
power of four with D ≤ n^{1/18}, […] and let g := ⌈D^{1/36}⌉" on the route through Theorem 5, and
"Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉" on the route through Corollary 26.  The reduction of
Theorem 17 cuts each residue class into chunks of at most `n²/√D` query pairs and splits `C` into
pieces of at most `⌈s/g⌉` vertices, where `s = ⌊√D⌋`.  A program finds all these numbers by
operations on natural numbers.

* `rootFloor e t` is `⌊t^{1/e}⌋` and `rootCeil e t` is `⌈t^{1/e}⌉` (`floor_rpow_inv`,
  `ceil_rpow_inv`); they are characterised by `x ≤ rootFloor e t ↔ x^e ≤ t` (`le_rootFloor_iff`) and
  `rootCeil e t ≤ g ↔ t ≤ g^e` (`rootCeil_le_iff`).
* The four functions `paramD₅Nat`, `paramG₅Nat`, `paramD₂₆Nat`, `paramG₂₆Nat` are the parameters
  of the proof of Theorem 19 (`paramD₅Nat_eq`, `paramG₅Nat_eq`, `paramD₂₆Nat_eq`, `paramG₂₆Nat_eq`);
  they are at least 1 and at most `n` or `D` (`paramD₂₆Nat_le`, `paramG₅Nat_le`, `paramG₂₆Nat_le`).
* The sizes of the proof of Theorem 17: `⌊n²/√D⌋ = ⌊√(n⁴/D)⌋` (`queryCapNat_eq`), `s` is the integer
  square root (`sOf_eq_sqrt`), and the rounded quotients are `a ⌈/⌉ b` (`pieceSizeNat_eq`,
  `numPiecesNat_eq`, `numChunks_eq`).  The middle part `C_k × ℤ_p` of an instance has at most `D`
  vertices (`pieceSize_mul_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Roots, rounded down and up -/




















































/-! ## The parameters of the proof of Theorem 19 -/
















































































/-! ## The sizes of the instances of the proof of Theorem 17 -/










/-- `queryCapNat n D` is `⌊n²/√D⌋`: both are the greatest `c` with `c² D ≤ n⁴`. -/
theorem queryCapNat_eq (n : ℕ) {D : ℕ} (hD : 1 ≤ D) : queryCapNat n D = queryCap n D := by
  refine (eq_of_forall_le_iff fun c => ?_).symm
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr (Nat.cast_pos.2 hD)
  rw [queryCap, Nat.le_floor_iff (by positivity), le_div_iff₀ hs, queryCapNat, Nat.le_sqrt',
    Nat.le_div_iff_mul_le hD, ← sq_le_sq₀ (by positivity) (by positivity), mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg D), ← pow_mul]
  exact_mod_cast Iff.rfl





















































end ThreeSumApsp.Spec

end
end

section


/-!
# The prime that is chosen (proof of Theorem 17)

`chosenPrime n D AB BC AC` is the first prime of the window `√D/2 ≤ p < √D` at which the count,
computed with Strassen's algorithm from the three lists of weights, is smallest.  Here
`triOf n AB BC AC` is the instance of Exact Triangle whose weights are read from the three lists:
`w(a,b)` at `a n + b` of `AB`, `w(b,c)` at `b n + c` of `BC`, `w(a,c)` at `a n + c` of `AC`.

* The computed count is the count of the proof of Theorem 17 at every prime of the window
  (`countOf_eq`), so the chosen prime is a selected prime in the sense of the proof of Theorem 17,
  "We select the prime with the smallest count" (`chosenPrime_isSelected`).  It lies between 2 and
  `⌊√D⌋` (`two_le_chosenPrime`, `chosenPrime_le_sqrt`).
* A program finds it in one pass over the primes: `bestOf f L i` is the best of the first `i`
  elements of a list (`bestOf_one`, `bestOf_succ`, `bestOf_length`).
* The paper bounds the weights by `n^ν`; a program has a bound `U`.  `kappaOf n U` is the least
  exponent `κ ≥ 1` with `U ≤ n^κ`, and with it the bound of the proof of Theorem 17 on the number
  `F(p)` of false positives, that is, of triples with `S(a,b,c) ≠ 0` and `p ∣ S(a,b,c)`, holds for
  the chosen prime (`F_chosenPrime_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The chosen prime -/






section Chosen

variable {n D : ℕ} (AB BC AC : List ℤ)








































end Chosen

/-! ## The smallest count, by one pass -/




















/-! ## False positives, in terms of a bound on the weights -/




/-- The exponent is at least 1. -/
theorem one_le_kappaOf (n U : ℕ) : 1 ≤ kappaOf n U := le_max_left _ _









/-- It is the least such exponent. -/
theorem kappaOf_le {n U : ℕ} (hn : 2 ≤ n) (hU : 1 ≤ U) {κ' : ℝ} (h1 : 1 ≤ κ')
    (h : (U : ℝ) ≤ (n : ℝ) ^ κ') : kappaOf n U ≤ κ' := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hU0 : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  refine max_le h1 ?_
  rw [div_le_iff₀ (Real.log_pos hn1), ← Real.log_rpow (by linarith)]
  exact Real.log_le_log hU0 h




















end ThreeSumApsp.Spec

end
end

section


/-!
# Orders of growth of counts

The time and the need of a program are natural numbers, given by explicit expressions in the
parameters of the input.  Only their order of growth is needed.  This file has one calculus
that reads the order of growth off such an expression, so that no constant is ever written out.

A *scale* (`Scale α ι`) fixes the parameters `x : α` for which bounds are claimed (`dom`) and some
quantities that are at least 1 there: the *bases* `base i`, whose powers are counted, and one more,
`hidden`, whose powers are not.  `s.SoftO t e` says that the count `t` is at most a constant times a
power of `hidden` times the monomial `∏ i, base i ^ e i`.  Three examples:

* bases `n`, `√D`, `κ log n` and `hidden = 1`: `s.SoftO t ![2, 1, 1]` is `t = O(n² √D κ log n)`;
* one base `√n` and `hidden = log n`: `s.SoftO t ![3]` is `t = Õ(n^{3/2})`;
* no base and `hidden = n U`: `s.SoftO t ![]` says that `t` is polynomially bounded.

So `SoftO` is `O` up to powers of `hidden`: it is `O` itself if `hidden = 1`, and `Õ` if `hidden` is
a logarithm.  The bounds hold on the whole domain and not only from some point on.

The exponents follow the expression.  A constant has the exponents 0 (`SoftO.const`), a sum the
larger ones (`SoftO.add`), a product their sum (`SoftO.mul`), a power their multiple (`SoftO.pow`).
Exponents may be raised (`SoftO.mono`), and the count may be replaced by a smaller one
(`SoftO.of_le`, `SoftO.of_forall_le`).  If every base is at most `2 ^ hidden`, the binary logarithm
of a bounded count has the exponents 0 (`SoftO.log2`).

The tactic `growth [h₁, h₂, …]` applies these rules from the outside to the inside of the
expression.  The facts `hᵢ` bound the quantities at which the rules stop: parameters, and functions
whose bound is a lemma of its own.  A function that is to be followed into its definition is
unfolded first.

A bound leaves the calculus by `SoftO.exists_le`, or as a `Dominated` statement by
`SoftO.dominated`.
-/

@[expose] public section

namespace ThreeSumApsp














namespace Scale










variable {α ι : Type*} [Fintype ι] (s : Scale α ι)









theorem mon_zero (x : α) : s.mon 0 x = 1 := by simp [mon]

theorem mon_add (e e' : ι → ℕ) (x : α) : s.mon (e + e') x = s.mon e x * s.mon e' x := by
  simp only [mon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem mon_smul (k : ℕ) (e : ι → ℕ) (x : α) : s.mon (k • e) x = s.mon e x ^ k := by
  simp only [mon, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm k]

theorem mon_single [DecidableEq ι] (i : ι) (x : α) : s.mon (Pi.single i 1) x = s.base i x := by
  simp [mon, Pi.single_apply, pow_ite]

variable {s} {x : α} {e e' : ι → ℕ} {c c' : ℕ}

/-- All bases are at least 1, so a monomial grows with its exponents. -/
theorem mon_le_mon (he : ∀ i, e i ≤ e' i) (hx : s.dom x) : s.mon e x ≤ s.mon e' x :=
  Finset.prod_le_prod (fun i _ => pow_nonneg (zero_le_one.trans (s.one_le_base i x hx)) _)
    fun i _ => pow_le_pow_right₀ (s.one_le_base i x hx) (he i)

/-- A monomial is at least 1. -/
theorem one_le_mon (e : ι → ℕ) (hx : s.dom x) : 1 ≤ s.mon e x :=
  (s.mon_zero x).ge.trans (mon_le_mon (fun _ => Nat.zero_le _) hx)

/-- The bound grows with all exponents. -/
theorem pow_mul_mon_le (hc : c ≤ c') (he : ∀ i, e i ≤ e' i) (hx : s.dom x) :
    s.hidden x ^ c * s.mon e x ≤ s.hidden x ^ c' * s.mon e' x :=
  mul_le_mul (pow_le_pow_right₀ (s.one_le_hidden x hx) hc) (mon_le_mon he hx)
    (zero_le_one.trans (one_le_mon e hx)) (pow_nonneg (zero_le_one.trans (s.one_le_hidden x hx)) _)

namespace SoftO

variable {t t₁ t₂ : α → ℕ} {e₁ e₂ : ι → ℕ}

/-! ### Entering and leaving -/





/-- A count that is at most a constant times a base. -/
theorem of_dominated_base [DecidableEq ι] (i : ι)
    (h : Dominated s.dom (fun x => (t x : ℝ)) (s.base i)) : s.SoftO t (Pi.single i 1) :=
  ⟨0, h.congr (fun _ _ => rfl) fun x _ => by rw [pow_zero, mon_single, one_mul]⟩

/-- A count that is at most a base. -/
theorem of_le_base [DecidableEq ι] (i : ι) (h : ∀ x, s.dom x → (t x : ℝ) ≤ s.base i x) :
    s.SoftO t (Pi.single i 1) :=
  of_dominated_base i (.of_le h)

/-- A count that is at most a constant times a monomial. -/
theorem of_dominated (h : Dominated s.dom (fun x => (t x : ℝ)) (s.mon e)) : s.SoftO t e :=
  ⟨0, by simpa only [pow_zero, one_mul] using h⟩







/-- If `hidden = 1`, the bound is the monomial. -/
theorem dominated (h : s.SoftO t e) (hhidden : ∀ x, s.dom x → s.hidden x = 1) :
    Dominated s.dom (fun x => (t x : ℝ)) (s.mon e) :=
  let ⟨_, h⟩ := h
  h.congr (fun _ _ => rfl) fun x hx => by rw [hhidden x hx, one_pow, one_mul]

/-! ### The rules -/

/-- The exponents may be raised. -/
theorem mono (h : s.SoftO t e) (he : ∀ i, e i ≤ e' i) : s.SoftO t e' :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_right fun _ hx => pow_mul_mon_le le_rfl he hx⟩

/-- A smaller count has the same bound. -/
theorem of_le (h : s.SoftO t₂ e) (hle : ∀ x, s.dom x → t₁ x ≤ t₂ x) : s.SoftO t₁ e :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_left fun x hx => Nat.cast_le.2 (hle x hx)⟩











/-- A constant has the exponents 0. -/
protected theorem const (k : ℕ) : s.SoftO (fun _ => k) 0 :=
  ⟨0, .const _ fun x _ => by rw [pow_zero, mon_zero, mul_one]⟩

/-- A sum has the larger exponents. -/
protected theorem add (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x + t₂ x) (e₁ ⊔ e₂) := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  refine ⟨max c₁ c₂, ?_⟩
  simpa only [Nat.cast_add] using
    (h₁.mono_right fun _ hx =>
      pow_mul_mon_le (e' := e₁ ⊔ e₂) (le_max_left _ _) (fun _ => le_sup_left) hx).add
      (h₂.mono_right fun _ hx => pow_mul_mon_le (le_max_right _ _) (fun _ => le_sup_right) hx)





/-- In a product the exponents add up. -/
protected theorem mul (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x * t₂ x) (e₁ + e₂) := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  refine ⟨c₁ + c₂, ?_⟩
  simpa only [Nat.cast_mul] using
    (h₁.mul h₂ (fun _ _ => Nat.cast_nonneg _) fun _ _ => Nat.cast_nonneg _).congr (fun _ _ => rfl)
      fun x _ => by rw [mon_add, pow_add, mul_mul_mul_comm]

/-- The `k`-th power multiplies the exponents by `k`. -/
protected theorem pow (h : s.SoftO t e) (k : ℕ) : s.SoftO (fun x => t x ^ k) (k • e) := by
  obtain ⟨c, h⟩ := h
  refine ⟨c * k, ?_⟩
  simpa only [Nat.cast_pow] using
    (h.pow (fun _ _ => Nat.cast_nonneg _) k).congr (fun _ _ => rfl)
      fun x _ => by rw [mon_smul, mul_pow, pow_mul]

/-- A maximum has the larger exponents. -/
protected theorem max (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => max (t₁ x) (t₂ x)) (e₁ ⊔ e₂) :=
  (h₁.add h₂).of_le fun _ _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)


























































end SoftO

end Scale








































end ThreeSumApsp

end
end

section


/-!
# Theorem 17: the time of each routine, up to a constant

The running time of the reduction of Theorem 17 is a sum of the time functions of its routines.  The
theorem bounds the additional time by "O(ν n³ log n/g + n^{ω+o(1)} D^{3/2} + n² D g)", where ν is
the exponent in `|w(e)| ≤ n^ν`; it is `κ` below.  The form for programs, `Claim.Theorem_17`, has,
here, Strassen's exponent `log₂ 7` in the second term.  This file bounds each
routine by a monomial in `n`, `√D` and `κ log n`, uniformly in `n`, `D`, `g`, `U` and `κ` under the
hypotheses of the theorem, and says which monomials are within which of the three terms.  No
constant is computed.

* `Steps t B` says that the number `t` of steps is `O(B)`, uniformly in the parameters.  Such bounds
  can be added and multiplied, and they absorb constant factors.
* Every time function is a polynomial in a few quantities, and each of these is at most a monomial
  `mon a b c = n^a (√D)^b (κ log n)^c`: `⌊√D⌋`, `g` and the size `⌈s/g⌉` of a piece are at most
  `√D`; `2^⌈log₂ n⌉ ≤ 2n`; the number of binary digits of `U ≤ n^κ` is `O(κ log n)` (section "The
  basic quantities").  So a routine takes `O(mon a b c)` steps (`StepsMon t a b c`), and the
  exponents are read off its time function, in the calculus `Scale.SoftO` on the scale `costScale`.
* All three bases are at least 1.  So a monomial is within the first term if its exponents are at
  most `(2, 1, 1)`, within the second if they are at most `(2, 3, 0)`, within the third if they are
  at most `(2, 2, 0)` (`Scale.SoftO.withinScans`, `Scale.SoftO.withinPrime`,
  `Scale.SoftO.withinBuild`).
* The choice of the prime runs through at most `√D` primes (`steps_chooseTime`).  The product of the
  two matrices is within the second term, as in the paper: Strassen's recursion makes
  `7^⌈log₂ n⌉ = O(n^{log₂ 7})` products of polynomials of degree below `p ≤ √D`
  (`steps_sqrt_mul_strSteps`).  The residues of the weights, computed bit by bit for each prime,
  take `O(√D n² κ log n)` steps, which is within the first term.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The hypotheses -/































namespace CostParams.Hyp

variable {θ : CostParams} (h : θ.Hyp)
include h

/-- `D ≥ 1`, as a natural number. -/
theorem one_le_D_nat : 1 ≤ θ.D := (by norm_num : 1 ≤ 16).trans h.hD16













/-- `g > 0`. -/
theorem g_pos : (0 : ℝ) < θ.g := zero_lt_one.trans_le h.one_le_g




/-- `√D > 0`. -/
theorem sqrt_pos : 0 < Real.sqrt θ.D := zero_lt_one.trans_le h.one_le_sqrt









/-- `√D g ≤ D ≤ n`. -/
theorem sqrt_mul_g_le : Real.sqrt θ.D * θ.g ≤ θ.n :=
  calc Real.sqrt θ.D * θ.g ≤ Real.sqrt θ.D * Real.sqrt θ.D := by
        gcongr
        exact h.hgD
    _ = θ.D := Real.mul_self_sqrt θ.D.cast_nonneg
    _ ≤ θ.n := Nat.cast_le.2 h.hDn

/-- `√D ≤ n`. -/
theorem sqrt_le_n : Real.sqrt θ.D ≤ θ.n :=
  (le_mul_of_one_le_right (Real.sqrt_nonneg _) h.one_le_g).trans h.sqrt_mul_g_le

end CostParams.Hyp

/-! ## Numbers of steps up to a constant -/






namespace Steps

variable {t t₁ t₂ : CostParams → ℕ} {B B₁ B₂ : CostParams → ℝ}

/-- A smaller number of steps. -/
theorem mono_left (h : Steps t₂ B) (hle : ∀ θ, θ.Hyp → t₁ θ ≤ t₂ θ) : Steps t₁ B :=
  Dominated.mono_left h fun θ hθ => Nat.cast_le.2 (hle θ hθ)

/-- A larger bound. -/
theorem mono_right (h : Steps t B₁) (hle : ∀ θ, θ.Hyp → B₁ θ ≤ B₂ θ) : Steps t B₂ :=
  Dominated.mono_right h hle

/-- `O(B) + O(B) = O(B)`. -/
protected theorem add (h₁ : Steps t₁ B) (h₂ : Steps t₂ B) : Steps (fun θ => t₁ θ + t₂ θ) B := by
  simpa only [Steps, Nat.cast_add] using Dominated.add h₁ h₂

/-- `O(B₁) · O(B₂) = O(B₁ B₂)`. -/
protected theorem mul (h₁ : Steps t₁ B₁) (h₂ : Steps t₂ B₂) :
    Steps (fun θ => t₁ θ * t₂ θ) fun θ => B₁ θ * B₂ θ := by
  simpa only [Steps, Nat.cast_mul] using
    Dominated.mul h₁ h₂ (fun _ _ => Nat.cast_nonneg _) fun _ _ => Nat.cast_nonneg _

/-- A constant factor is absorbed. -/
theorem const_mul {c : ℕ} (h : Steps t B) : Steps (fun θ => c * t θ) B := by
  simpa only [Steps, Nat.cast_mul] using Dominated.const_mul h c.cast_nonneg

/-- A constant number of steps is `O(B)` if `B ≥ 1`. -/
protected theorem const {c : ℕ} (hB : ∀ θ, θ.Hyp → 1 ≤ B θ) : Steps (fun _ => c) B :=
  Dominated.const _ hB

end Steps

/-! ## Monomials -/












theorem mon_eq (a b c : ℕ) (θ : CostParams) :
    mon a b c θ = (θ.n : ℝ) ^ a * Real.sqrt θ.D ^ b * (θ.κ * Real.log θ.n) ^ c := by
  simp [Scale.mon, costScale, Scale.ofBases, Fin.prod_univ_three]




/-- A bound by a monomial, as a bound up to a constant. -/
theorem steps_of_softO {t : CostParams → ℕ} {e : Fin 3 → ℕ} (h : costScale.SoftO t e) :
    Steps t (costScale.mon e) :=
  h.dominated fun _ _ => rfl

/-! ## The basic quantities -/

/-- The number of vertices per part. -/
theorem steps_n : StepsMon (fun θ => θ.n) 1 0 0 :=
  (Scale.SoftO.of_le_base 0 fun _ _ => le_rfl).mono (by decide)

/-- `s = ⌊√D⌋ ≤ √D`. -/
theorem steps_sqrt : StepsMon (fun θ => Nat.sqrt θ.D) 0 1 0 :=
  (Scale.SoftO.of_le_base 1 fun _ _ => Real.nat_sqrt_le_real_sqrt).mono (by decide)

/-- `D = (√D)²`. -/
theorem steps_D : StepsMon (fun θ => θ.D) 0 2 0 :=
  .of_dominated <| .of_le fun θ _ => by
    simp only [mon_eq, pow_zero, mul_one, one_mul, Real.sq_sqrt θ.D.cast_nonneg, le_refl]

/-- `g ≤ √D`. -/
private theorem steps_g : StepsMon (fun θ => θ.g) 0 1 0 :=
  (Scale.SoftO.of_le_base (s := costScale) 1 fun _ hθ => hθ.hgD).mono (by decide)

/-- `2^⌈log₂ n⌉ ≤ 2n`. -/
private theorem steps_two_pow_clog : StepsMon (fun θ => 2 ^ Nat.clog 2 θ.n) 1 0 0 :=
  (by first
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply steps_n
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div);
          (·
              first
              | decide
              | exact isEmptyElim))
      |
        ((fail_if_success
              (fail_if_success
                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                    (on_goal 1 =>
                        ((repeat'
                              with_reducible
                                first
                                | exact ThreeSumApsp.Scale.SoftO.const _
                                | apply steps_n
                                | apply ThreeSumApsp.Scale.SoftO.add
                                | apply ThreeSumApsp.Scale.SoftO.mul
                                | apply ThreeSumApsp.Scale.SoftO.pow
                                | apply ThreeSumApsp.Scale.SoftO.max
                                | apply ThreeSumApsp.Scale.SoftO.sub
                                | apply ThreeSumApsp.Scale.SoftO.div);
                          (done))))));
          (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
          (all_goals
              try
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (·
                      repeat'
                        with_reducible
                          first
                          | exact ThreeSumApsp.Scale.SoftO.const _
                          | apply steps_n
                          | apply ThreeSumApsp.Scale.SoftO.add
                          | apply ThreeSumApsp.Scale.SoftO.mul
                          | apply ThreeSumApsp.Scale.SoftO.pow
                          | apply ThreeSumApsp.Scale.SoftO.max
                          | apply ThreeSumApsp.Scale.SoftO.sub
                          | apply ThreeSumApsp.Scale.SoftO.div);
                  (· decide))))
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply steps_n
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div)) : StepsMon (fun θ => 2 * θ.n) 1 0 0).of_le fun _ hθ =>
    Nat.pow_clog_le_mul one_lt_two hθ.one_le_n_nat

/-- `⌈log₂ n⌉ ≤ 2^⌈log₂ n⌉`. -/
private theorem steps_clog : StepsMon (fun θ => Nat.clog 2 θ.n) 1 0 0 :=
  steps_two_pow_clog.of_le fun _ _ => Nat.lt_two_pow_self.le

/-- The number of binary digits of `U ≤ n^κ` is `O(κ log n)`: `2^{len - 1} ≤ U` gives
`(len - 1) log 2 ≤ κ log n`. -/
private theorem steps_bitLen : StepsMon (fun θ => bitLen θ.U) 0 0 1 := by
  refine .of_dominated (Dominated.of_le_const_mul (C := 3) (by norm_num) fun θ hθ => ?_)
  simp only [mon_eq, pow_zero, one_mul, pow_one]
  have hΛ : 1 ≤ θ.κ * Real.log θ.n := hθ.one_le_κ_mul_log
  rcases Nat.eq_zero_or_pos θ.U with hU | hU
  · rw [hU, bitLen, Nat.size_zero, Nat.cast_zero]
    linarith [hΛ]
  · have hlen : 1 ≤ bitLen θ.U := Nat.size_pos.2 hU
    have hpow : 2 ^ (bitLen θ.U - 1) ≤ θ.U := Nat.lt_size.1 (Nat.sub_lt hlen one_pos)
    have hlog := Real.log_le_log (by positivity)
      (le_trans (by exact_mod_cast hpow : (2 : ℝ) ^ (bitLen θ.U - 1) ≤ θ.U) hθ.hUn)
    rw [Real.log_pow, Real.log_rpow (zero_lt_one.trans_le hθ.one_le_n), Nat.cast_sub hlen,
      Nat.cast_one] at hlog
    have hhalf := mul_le_mul_of_nonneg_left Real.one_half_lt_log_two.le
      (sub_nonneg.2 (Nat.one_le_cast.2 hlen : (1 : ℝ) ≤ bitLen θ.U))
    -- `(len - 1)/2 ≤ (len - 1) log 2 ≤ κ log n` and `1 ≤ κ log n`.
    linarith [hlog, hhalf, hΛ]

/-- A piece has `⌈s/g⌉ ≤ s` vertices. -/
private theorem steps_pieceSizeNat : StepsMon (fun θ => pieceSizeNat θ.D θ.g) 0 1 0 :=
  steps_sqrt.of_le fun _ hθ => (Nat.ceilDiv_le_iff hθ.hg).2 (Nat.le_mul_of_pos_right _ hθ.hg)

/-- `⌊n²/√D⌋ ≤ n²/√D`. -/
theorem cast_queryCapNat_le {θ : CostParams} (hθ : θ.Hyp) :
    (queryCapNat θ.n θ.D : ℝ) ≤ (θ.n : ℝ) ^ 2 / Real.sqrt θ.D := by
  rw [queryCapNat_eq θ.n hθ.one_le_D_nat]
  exact Nat.floor_le (by positivity)

/-- `⌊n²/√D⌋ ≤ n²`. -/
private theorem steps_queryCapNat : StepsMon (fun θ => queryCapNat θ.n θ.D) 2 0 0 :=
  .of_dominated <| .of_le fun θ hθ => (cast_queryCapNat_le hθ).trans (by
    simpa only [mon_eq, pow_zero, mul_one] using div_le_self (by positivity) hθ.one_le_sqrt)

/-! ## The routines -/

/-- The number of binary digits of `U`. -/
theorem steps_tBitLen : StepsMon (fun θ => tBitLen θ.U) 0 0 1 := by
  unfold tBitLen
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_bitLen
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_bitLen
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_bitLen
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_bitLen
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The table of the doubles of the prime. -/
theorem steps_tDblTable : StepsMon (fun θ => tDblTable (bitLen θ.U)) 0 0 1 := by
  unfold tDblTable
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_bitLen
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_bitLen
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_bitLen
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_bitLen
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The residues of the `n²` weights of one kind: `O(log U)` steps for each. -/
theorem steps_tResidues : StepsMon (fun θ => tResidues (θ.n * θ.n) (bitLen θ.U)) 2 0 1 := by
  unfold tResidues tResid
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_bitLen
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_n
                            | apply steps_bitLen
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_n
                      | apply steps_bitLen
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_bitLen
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- Sorting the pairs into classes. -/
theorem steps_tClasses : StepsMon (fun θ => tClasses θ.n (Nat.sqrt θ.D)) 2 1 0 := by
  unfold tClasses
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_sqrt
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_n
                            | apply steps_sqrt
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_n
                      | apply steps_sqrt
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_sqrt
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- Cutting the classes into chunks. -/
theorem steps_tChunks : StepsMon (fun θ => tChunks (Nat.sqrt θ.D) (4 * θ.n * θ.g)) 1 1 0 := by
  unfold tChunks
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_sqrt
              | apply steps_g
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_n
                            | apply steps_sqrt
                            | apply steps_g
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_n
                      | apply steps_sqrt
                      | apply steps_g
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_sqrt
              | apply steps_g
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The list of the primes in `[√D/2, √D)`. -/
private theorem steps_tPrimes : StepsMon (fun θ => tPrimes θ.D) 0 3 0 := by
  unfold tPrimes
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_sqrt
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_sqrt
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_sqrt
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_sqrt
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- Writing the matrix `X` of an instance takes `O(nD)` steps. -/
theorem steps_tWriteX : StepsMon (fun θ => tWriteX θ.n θ.D (pieceSizeNat θ.D θ.g)) 1 2 0 := by
  unfold tWriteX
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_D
              | apply steps_pieceSizeNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_n
                            | apply steps_D
                            | apply steps_pieceSizeNat
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_n
                      | apply steps_D
                      | apply steps_pieceSizeNat
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_D
              | apply steps_pieceSizeNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- Writing the matrix `Y` of an instance takes `O(nD)` steps. -/
theorem steps_tWriteY : StepsMon (fun θ => tWriteY θ.n θ.D (pieceSizeNat θ.D θ.g)) 1 2 0 := by
  unfold tWriteY
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_D
              | apply steps_pieceSizeNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_n
                            | apply steps_D
                            | apply steps_pieceSizeNat
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_n
                      | apply steps_D
                      | apply steps_pieceSizeNat
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_D
              | apply steps_pieceSizeNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The table of the sizes of the blocks. -/
private theorem steps_tSzTable : StepsMon (fun θ => tSzTable (Nat.clog 2 θ.n)) 1 0 0 := by
  unfold tSzTable
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_clog
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_clog
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_clog
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_clog
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- One of the matrices `P`, `Q` over `ℤ[x]/(x^p - 1)` in Z-order: `O(n² √D)`. -/
private theorem steps_buildZTime :
    StepsMon (fun θ => buildZTime θ.n (2 ^ Nat.clog 2 θ.n) (Nat.sqrt θ.D)) 2 1 0 := by
  unfold buildZTime
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_sqrt
              | apply steps_two_pow_clog
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_n
                            | apply steps_sqrt
                            | apply steps_two_pow_clog
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_n
                      | apply steps_sqrt
                      | apply steps_two_pow_clog
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_sqrt
              | apply steps_two_pow_clog
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- Reading the count off the product. -/
private theorem steps_countZeroTime : StepsMon (fun θ => countZeroTime θ.n) 2 0 0 := by
  unfold countZeroTime
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_n
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_n
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- `⌊n²/√D⌋`, by counting up. -/
theorem steps_tQueryCapNat : StepsMon (fun θ => tQueryCapNat θ.n θ.D) 2 0 0 := by
  unfold tQueryCapNat
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_queryCapNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_queryCapNat
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_queryCapNat
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_queryCapNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The number `⌈s/g⌉` of vertices of a piece, by counting up. -/
theorem steps_tCeilDiv_piece : StepsMon (fun θ => tCeilDiv (Nat.sqrt θ.D) θ.g) 0 1 0 := by
  have hpiece : StepsMon (fun θ => Nat.sqrt θ.D ⌈/⌉ θ.g) 0 1 0 := steps_pieceSizeNat
  unfold tCeilDiv
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply hpiece
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply hpiece
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply hpiece
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply hpiece
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The number of pieces, by counting up. -/
theorem steps_tCeilDiv_num : StepsMon (fun θ => tCeilDiv θ.n (pieceSizeNat θ.D θ.g)) 1 0 0 := by
  have hnum : StepsMon (fun θ => θ.n ⌈/⌉ pieceSizeNat θ.D θ.g) 1 0 0 :=
    steps_n.of_le fun θ hθ => by
      have hsqrt : 0 < Nat.sqrt θ.D := Nat.sqrt_pos.2 ((by norm_num : 0 < 16).trans_le hθ.hD16)
      have hpiece : 0 < pieceSizeNat θ.D θ.g := (Nat.lt_ceilDiv_iff hθ.hg).2 (by rwa [zero_mul])
      exact (Nat.ceilDiv_le_iff hpiece).2 (Nat.le_mul_of_pos_right _ hpiece)
  unfold tCeilDiv
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply hnum
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply hnum
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply hnum
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply hnum
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-! ## The three terms of the bound dominate the monomials -/

/-- `D^{3/2} = (√D)³`. -/
private theorem rpow_three_half (D : ℕ) : (D : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt D ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul D.cast_nonneg]
  norm_num

/-- `n² √D κ log n ≤ κ n³ log n/g`, because `√D g ≤ n`. -/
private theorem mon_le_termScans {θ : CostParams} (hθ : θ.Hyp) :
    mon 2 1 1 θ ≤ termScans θ.n θ.g θ.κ := by
  have hκ : 0 ≤ θ.κ := zero_le_one.trans hθ.hκ
  rw [termScans, le_div_iff₀ hθ.g_pos]
  calc mon 2 1 1 θ * θ.g
      = (θ.n : ℝ) ^ 2 * θ.κ * Real.log θ.n * (Real.sqrt θ.D * θ.g) := by
        rw [mon_eq]
        ring
    _ ≤ (θ.n : ℝ) ^ 2 * θ.κ * Real.log θ.n * θ.n := by
        gcongr _ * ?_
        exact hθ.sqrt_mul_g_le
    _ = θ.κ * (θ.n : ℝ) ^ 3 * Real.log θ.n := by ring

/-- `n² (√D)³ ≤ n^{log₂ 7} D^{3/2}`. -/
private theorem mon_le_termPrime {θ : CostParams} (hθ : θ.Hyp) :
    mon 2 3 0 θ ≤ termPrime strassen θ.n θ.D := by
  have htwo : (2 : ℝ) ≤ Real.logb 2 7 := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
    norm_num
  rw [termPrime, strassen, rpow_three_half, mon_eq, pow_zero, mul_one, ← Real.rpow_ofNat]
  gcongr
  exact hθ.one_le_n

/-- `n² (√D)² ≤ n² D g`. -/
private theorem mon_le_termBuild {θ : CostParams} (hθ : θ.Hyp) :
    mon 2 2 0 θ ≤ termBuild θ.n θ.D θ.g := by
  rw [termBuild, mon_eq, pow_zero, mul_one, Real.sq_sqrt θ.D.cast_nonneg]
  exact le_mul_of_one_le_right (by positivity) hθ.one_le_g





/-- The first term is not negative. -/
private theorem termScans_nonneg {θ : CostParams} (hθ : θ.Hyp) : 0 ≤ termScans θ.n θ.g θ.κ := by
  have hκ : 0 ≤ θ.κ := zero_le_one.trans hθ.hκ
  unfold termScans
  positivity

/-- The second term is not negative. -/
private theorem termPrime_nonneg (θ : CostParams) : 0 ≤ termPrime strassen θ.n θ.D := by
  unfold termPrime strassen
  positivity

/-- The third term is not negative. -/
private theorem termBuild_nonneg (θ : CostParams) : 0 ≤ termBuild θ.n θ.D θ.g := by
  unfold termBuild
  positivity

/-- The sum is not negative. -/
theorem budget_nonneg {θ : CostParams} (hθ : θ.Hyp) : 0 ≤ budget θ :=
  add_nonneg (add_nonneg (termScans_nonneg hθ) (termPrime_nonneg θ)) (termBuild_nonneg θ)

/-- The first term is at most the sum. -/
theorem termScans_le_budget (θ : CostParams) : termScans θ.n θ.g θ.κ ≤ budget θ := by
  unfold budget
  linarith [termPrime_nonneg θ, termBuild_nonneg θ]

/-- The second term is at most the sum. -/
private theorem termPrime_le_budget {θ : CostParams} (hθ : θ.Hyp) :
    termPrime strassen θ.n θ.D ≤ budget θ := by
  unfold budget
  linarith [termScans_nonneg hθ, termBuild_nonneg θ]

/-- The third term is at most the sum. -/
theorem termBuild_le_budget {θ : CostParams} (hθ : θ.Hyp) :
    termBuild θ.n θ.D θ.g ≤ budget θ := by
  unfold budget
  linarith [termScans_nonneg hθ, termPrime_nonneg θ]

section within

variable {t : CostParams → ℕ} {e : Fin 3 → ℕ}

/-- Within the first term, `κ n³ log n/g`. -/
theorem _root_.ThreeSumApsp.Scale.SoftO.withinScans (h : costScale.SoftO t e)
    (he : ∀ i, e i ≤ ![2, 1, 1] i := by decide) : Steps t budget :=
  (steps_of_softO (h.mono he)).mono_right fun θ hθ =>
    (mon_le_termScans hθ).trans (termScans_le_budget θ)

/-- Within the second term, `n^{log₂ 7} D^{3/2}`. -/
theorem _root_.ThreeSumApsp.Scale.SoftO.withinPrime (h : costScale.SoftO t e)
    (he : ∀ i, e i ≤ ![2, 3, 0] i := by decide) : Steps t budget :=
  (steps_of_softO (h.mono he)).mono_right fun _ hθ =>
    (mon_le_termPrime hθ).trans (termPrime_le_budget hθ)

/-- Within the third term, `n² D g`. -/
theorem _root_.ThreeSumApsp.Scale.SoftO.withinBuild (h : costScale.SoftO t e)
    (he : ∀ i, e i ≤ ![2, 2, 0] i := by decide) : Steps t budget :=
  (steps_of_softO (h.mono he)).mono_right fun _ hθ =>
    (mon_le_termBuild hθ).trans (termBuild_le_budget hθ)

end within

namespace Steps

variable {t₁ t₂ m : CostParams → ℕ} {B : CostParams → ℝ}

/-- A factor is distributed over a sum. -/
theorem mul_add (h₁ : Steps (fun θ => m θ * t₁ θ) B) (h₂ : Steps (fun θ => m θ * t₂ θ) B) :
    Steps (fun θ => m θ * (t₁ θ + t₂ θ)) B :=
  (h₁.add h₂).mono_left fun _ _ => (Nat.mul_add _ _ _).le

end Steps

/-! ## The choice of the prime -/

/-- A sequence with `a(j+1) = 7 a(j) + b 4^j x + c` grows like `7^j`. -/
private theorem le_mul_seven_pow {a : ℕ → ℕ} {b c x : ℕ}
    (h : ∀ j, a (j + 1) = 7 * a j + b * (4 ^ j * x) + c) (j : ℕ) :
    a j + b * (4 ^ j * x) + c ≤ (a 0 + a 1) * 7 ^ j := by
  induction j with
  | zero =>
    rw [h 0]
    omega
  | succ j ih =>
    rw [h j, pow_succ 4, pow_succ 7]
    -- `7 a(j) + 5 b 4^j x + 2c ≤ 7 (a(j) + b 4^j x + c)`.
    linarith [ih, Nat.zero_le (b * (4 ^ j * x)), Nat.zero_le c]

/-- `7^⌈log₂ n⌉ = O(n^{log₂ 7})`. -/
private theorem steps_seven_pow_clog :
    Steps (fun θ => 7 ^ Nat.clog 2 θ.n) fun θ => (θ.n : ℝ) ^ Real.logb 2 7 :=
  Dominated.of_le_const_mul (C := 7) (by norm_num) fun θ hθ => by
    have hn : 1 ≤ θ.n := hθ.one_le_n_nat
    exact_mod_cast seven_pow_clog_le hn

/-- Strassen's recursion on matrices over `ℤ[x]/(x^p - 1)`, for all primes of the range:
`O(√D · 7^⌈log₂ n⌉ p²) = O(n^{log₂ 7} D^{3/2})`. -/
private theorem steps_sqrt_mul_strSteps :
    Steps (fun θ => Nat.sqrt θ.D * strSteps (Nat.sqrt θ.D) (Nat.clog 2 θ.n)) budget := by
  -- `strSteps p 0` is a quadratic polynomial in `p`, and
  -- `strSteps p (j + 1) = 7 strSteps p j + b 4^j p + c` with two numerals `b`, `c`.
  have hbase : StepsMon (fun θ => strSteps (Nat.sqrt θ.D) 0 + strSteps (Nat.sqrt θ.D) 1) 0 2 0 := by
    simp only [strSteps]
    first
    |
      ((apply ThreeSumApsp.Scale.SoftO.mono);
        (·
            repeat'
              with_reducible
                first
                | exact ThreeSumApsp.Scale.SoftO.const _
                | apply steps_sqrt
                | apply ThreeSumApsp.Scale.SoftO.add
                | apply ThreeSumApsp.Scale.SoftO.mul
                | apply ThreeSumApsp.Scale.SoftO.pow
                | apply ThreeSumApsp.Scale.SoftO.max
                | apply ThreeSumApsp.Scale.SoftO.sub
                | apply ThreeSumApsp.Scale.SoftO.div);
        (·
            first
            | decide
            | exact isEmptyElim))
    |
      ((fail_if_success
            (fail_if_success
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (on_goal 1 =>
                      ((repeat'
                            with_reducible
                              first
                              | exact ThreeSumApsp.Scale.SoftO.const _
                              | apply steps_sqrt
                              | apply ThreeSumApsp.Scale.SoftO.add
                              | apply ThreeSumApsp.Scale.SoftO.mul
                              | apply ThreeSumApsp.Scale.SoftO.pow
                              | apply ThreeSumApsp.Scale.SoftO.max
                              | apply ThreeSumApsp.Scale.SoftO.sub
                              | apply ThreeSumApsp.Scale.SoftO.div);
                        (done))))));
        (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
        (all_goals
            try
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (·
                    repeat'
                      with_reducible
                        first
                        | exact ThreeSumApsp.Scale.SoftO.const _
                        | apply steps_sqrt
                        | apply ThreeSumApsp.Scale.SoftO.add
                        | apply ThreeSumApsp.Scale.SoftO.mul
                        | apply ThreeSumApsp.Scale.SoftO.pow
                        | apply ThreeSumApsp.Scale.SoftO.max
                        | apply ThreeSumApsp.Scale.SoftO.sub
                        | apply ThreeSumApsp.Scale.SoftO.div);
                (· decide))))
    |
      ((apply ThreeSumApsp.Scale.SoftO.mono);
        (·
            repeat'
              with_reducible
                first
                | exact ThreeSumApsp.Scale.SoftO.const _
                | apply steps_sqrt
                | apply ThreeSumApsp.Scale.SoftO.add
                | apply ThreeSumApsp.Scale.SoftO.mul
                | apply ThreeSumApsp.Scale.SoftO.pow
                | apply ThreeSumApsp.Scale.SoftO.max
                | apply ThreeSumApsp.Scale.SoftO.sub
                | apply ThreeSumApsp.Scale.SoftO.div))
  refine (((steps_of_softO steps_sqrt).mul ((steps_of_softO hbase).mul
    steps_seven_pow_clog)).mono_left fun θ _ => ?_).mono_right fun θ hθ => ?_
  · exact Nat.mul_le_mul_left _ (le_trans (by omega)
      (le_mul_seven_pow (a := strSteps (Nat.sqrt θ.D)) (fun _ => rfl) (Nat.clog 2 θ.n)))
  · refine le_trans (le_of_eq ?_) (termPrime_le_budget hθ)
    simp only [termPrime, strassen, rpow_three_half, mon_eq]
    ring

/-- The counts for all primes of the range: at most `√D` times the time of one count and a constant
`k`.  The summands stand in the order of `countTime`. -/
private theorem steps_sqrt_mul_countTime {k : ℕ} :
    Steps (fun θ => Nat.sqrt θ.D *
      (countTime θ.n (Nat.sqrt θ.D) (bitLen θ.U) (Nat.clog 2 θ.n) + k)) budget :=
  -- the table of doubles
  (steps_sqrt.mul steps_tDblTable).withinScans
  -- the residues of the three kinds of weights
  |>.mul_add (by first
                 |
                   ((apply ThreeSumApsp.Scale.SoftO.mono);
                     (·
                         repeat'
                           with_reducible
                             first
                             | exact ThreeSumApsp.Scale.SoftO.const _
                             | apply steps_sqrt
                             | apply steps_tResidues
                             | apply ThreeSumApsp.Scale.SoftO.add
                             | apply ThreeSumApsp.Scale.SoftO.mul
                             | apply ThreeSumApsp.Scale.SoftO.pow
                             | apply ThreeSumApsp.Scale.SoftO.max
                             | apply ThreeSumApsp.Scale.SoftO.sub
                             | apply ThreeSumApsp.Scale.SoftO.div);
                     (·
                         first
                         | decide
                         | exact isEmptyElim))
                 |
                   ((fail_if_success
                         (fail_if_success
                             ((apply ThreeSumApsp.Scale.SoftO.mono);
                               (on_goal 1 =>
                                   ((repeat'
                                         with_reducible
                                           first
                                           | exact ThreeSumApsp.Scale.SoftO.const _
                                           | apply steps_sqrt
                                           | apply steps_tResidues
                                           | apply ThreeSumApsp.Scale.SoftO.add
                                           | apply ThreeSumApsp.Scale.SoftO.mul
                                           | apply ThreeSumApsp.Scale.SoftO.pow
                                           | apply ThreeSumApsp.Scale.SoftO.max
                                           | apply ThreeSumApsp.Scale.SoftO.sub
                                           | apply ThreeSumApsp.Scale.SoftO.div);
                                     (done))))));
                     (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
                     (all_goals
                         try
                           ((apply ThreeSumApsp.Scale.SoftO.mono);
                             (·
                                 repeat'
                                   with_reducible
                                     first
                                     | exact ThreeSumApsp.Scale.SoftO.const _
                                     | apply steps_sqrt
                                     | apply steps_tResidues
                                     | apply ThreeSumApsp.Scale.SoftO.add
                                     | apply ThreeSumApsp.Scale.SoftO.mul
                                     | apply ThreeSumApsp.Scale.SoftO.pow
                                     | apply ThreeSumApsp.Scale.SoftO.max
                                     | apply ThreeSumApsp.Scale.SoftO.sub
                                     | apply ThreeSumApsp.Scale.SoftO.div);
                             (· decide))))
                 |
                   ((apply ThreeSumApsp.Scale.SoftO.mono);
                     (·
                         repeat'
                           with_reducible
                             first
                             | exact ThreeSumApsp.Scale.SoftO.const _
                             | apply steps_sqrt
                             | apply steps_tResidues
                             | apply ThreeSumApsp.Scale.SoftO.add
                             | apply ThreeSumApsp.Scale.SoftO.mul
                             | apply ThreeSumApsp.Scale.SoftO.pow
                             | apply ThreeSumApsp.Scale.SoftO.max
                             | apply ThreeSumApsp.Scale.SoftO.sub
                             | apply ThreeSumApsp.Scale.SoftO.div)) : StepsMon _ 2 1 1).withinScans
  -- the table for the Z-order
  |>.mul_add (by first
                 |
                   ((apply ThreeSumApsp.Scale.SoftO.mono);
                     (·
                         repeat'
                           with_reducible
                             first
                             | exact ThreeSumApsp.Scale.SoftO.const _
                             | apply steps_sqrt
                             | apply steps_two_pow_clog
                             | apply ThreeSumApsp.Scale.SoftO.add
                             | apply ThreeSumApsp.Scale.SoftO.mul
                             | apply ThreeSumApsp.Scale.SoftO.pow
                             | apply ThreeSumApsp.Scale.SoftO.max
                             | apply ThreeSumApsp.Scale.SoftO.sub
                             | apply ThreeSumApsp.Scale.SoftO.div);
                     (·
                         first
                         | decide
                         | exact isEmptyElim))
                 |
                   ((fail_if_success
                         (fail_if_success
                             ((apply ThreeSumApsp.Scale.SoftO.mono);
                               (on_goal 1 =>
                                   ((repeat'
                                         with_reducible
                                           first
                                           | exact ThreeSumApsp.Scale.SoftO.const _
                                           | apply steps_sqrt
                                           | apply steps_two_pow_clog
                                           | apply ThreeSumApsp.Scale.SoftO.add
                                           | apply ThreeSumApsp.Scale.SoftO.mul
                                           | apply ThreeSumApsp.Scale.SoftO.pow
                                           | apply ThreeSumApsp.Scale.SoftO.max
                                           | apply ThreeSumApsp.Scale.SoftO.sub
                                           | apply ThreeSumApsp.Scale.SoftO.div);
                                     (done))))));
                     (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
                     (all_goals
                         try
                           ((apply ThreeSumApsp.Scale.SoftO.mono);
                             (·
                                 repeat'
                                   with_reducible
                                     first
                                     | exact ThreeSumApsp.Scale.SoftO.const _
                                     | apply steps_sqrt
                                     | apply steps_two_pow_clog
                                     | apply ThreeSumApsp.Scale.SoftO.add
                                     | apply ThreeSumApsp.Scale.SoftO.mul
                                     | apply ThreeSumApsp.Scale.SoftO.pow
                                     | apply ThreeSumApsp.Scale.SoftO.max
                                     | apply ThreeSumApsp.Scale.SoftO.sub
                                     | apply ThreeSumApsp.Scale.SoftO.div);
                             (· decide))))
                 |
                   ((apply ThreeSumApsp.Scale.SoftO.mono);
                     (·
                         repeat'
                           with_reducible
                             first
                             | exact ThreeSumApsp.Scale.SoftO.const _
                             | apply steps_sqrt
                             | apply steps_two_pow_clog
                             | apply ThreeSumApsp.Scale.SoftO.add
                             | apply ThreeSumApsp.Scale.SoftO.mul
                             | apply ThreeSumApsp.Scale.SoftO.pow
                             | apply ThreeSumApsp.Scale.SoftO.max
                             | apply ThreeSumApsp.Scale.SoftO.sub
                             | apply ThreeSumApsp.Scale.SoftO.div)) : StepsMon _ 1 1 0).withinScans
  -- the table of the sizes of the blocks
  |>.mul_add (steps_sqrt.mul steps_tSzTable).withinScans
  -- the matrices `P` and `Q`
  |>.mul_add (by first
                 |
                   ((apply ThreeSumApsp.Scale.SoftO.mono);
                     (·
                         repeat'
                           with_reducible
                             first
                             | exact ThreeSumApsp.Scale.SoftO.const _
                             | apply steps_sqrt
                             | apply steps_buildZTime
                             | apply ThreeSumApsp.Scale.SoftO.add
                             | apply ThreeSumApsp.Scale.SoftO.mul
                             | apply ThreeSumApsp.Scale.SoftO.pow
                             | apply ThreeSumApsp.Scale.SoftO.max
                             | apply ThreeSumApsp.Scale.SoftO.sub
                             | apply ThreeSumApsp.Scale.SoftO.div);
                     (·
                         first
                         | decide
                         | exact isEmptyElim))
                 |
                   ((fail_if_success
                         (fail_if_success
                             ((apply ThreeSumApsp.Scale.SoftO.mono);
                               (on_goal 1 =>
                                   ((repeat'
                                         with_reducible
                                           first
                                           | exact ThreeSumApsp.Scale.SoftO.const _
                                           | apply steps_sqrt
                                           | apply steps_buildZTime
                                           | apply ThreeSumApsp.Scale.SoftO.add
                                           | apply ThreeSumApsp.Scale.SoftO.mul
                                           | apply ThreeSumApsp.Scale.SoftO.pow
                                           | apply ThreeSumApsp.Scale.SoftO.max
                                           | apply ThreeSumApsp.Scale.SoftO.sub
                                           | apply ThreeSumApsp.Scale.SoftO.div);
                                     (done))))));
                     (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
                     (all_goals
                         try
                           ((apply ThreeSumApsp.Scale.SoftO.mono);
                             (·
                                 repeat'
                                   with_reducible
                                     first
                                     | exact ThreeSumApsp.Scale.SoftO.const _
                                     | apply steps_sqrt
                                     | apply steps_buildZTime
                                     | apply ThreeSumApsp.Scale.SoftO.add
                                     | apply ThreeSumApsp.Scale.SoftO.mul
                                     | apply ThreeSumApsp.Scale.SoftO.pow
                                     | apply ThreeSumApsp.Scale.SoftO.max
                                     | apply ThreeSumApsp.Scale.SoftO.sub
                                     | apply ThreeSumApsp.Scale.SoftO.div);
                             (· decide))))
                 |
                   ((apply ThreeSumApsp.Scale.SoftO.mono);
                     (·
                         repeat'
                           with_reducible
                             first
                             | exact ThreeSumApsp.Scale.SoftO.const _
                             | apply steps_sqrt
                             | apply steps_buildZTime
                             | apply ThreeSumApsp.Scale.SoftO.add
                             | apply ThreeSumApsp.Scale.SoftO.mul
                             | apply ThreeSumApsp.Scale.SoftO.pow
                             | apply ThreeSumApsp.Scale.SoftO.max
                             | apply ThreeSumApsp.Scale.SoftO.sub
                             | apply ThreeSumApsp.Scale.SoftO.div)) : StepsMon _ 2 2 0).withinPrime
  -- their product
  |>.mul_add steps_sqrt_mul_strSteps
  -- the count
  |>.mul_add (steps_sqrt.mul steps_countZeroTime).withinScans
  -- calls and returns
  |>.mul_add (steps_sqrt.mul (.const _)).withinScans
  |>.mul_add (steps_sqrt.mul (.const _)).withinScans

/-- **The choice of the prime** is within the bound.  The summands stand in the order of
`chooseTime`: the list of the primes, the number of binary digits of `U`, `⌈log₂ n⌉`, and the
counts. -/
theorem steps_chooseTime : Steps (fun θ => chooseTime θ.n θ.U θ.D) budget :=
  steps_tPrimes.withinPrime
  |>.add steps_tBitLen.withinScans
  |>.add ((Scale.SoftO.const _).mul steps_clog).withinScans
  |>.add steps_sqrt_mul_countTime
  |>.add (Scale.SoftO.const _).withinScans

end Light.Sec3

end
end

section


/-!
# The time of the host of Theorem 17 obeys the bound of Theorem 17

Theorem 17 reduces Exact Triangle to at most `4ng` instances "plus O(ν n³ log n/g + n^{ω+o(1)}
D^{3/2} + n² D g) additional time".  The form for programs, `Claim.Theorem_17`, has, here,
Strassen's exponent in the second term; its right side is `bound17`.  The time
function of the host is the time of `4ng` calls of the solver plus a rest, its time over a solver
that takes no time (`hostTime_eq`), and the rest is bounded term by term, up to a constant.

* The parameters, the choice of the prime, the residues, the classes and the chunks are within the
  three terms of the bound (`steps_hostSetup`, `steps_chooseTime`, `steps_tResidues`,
  `steps_tClasses`, `steps_tChunks`).
* Writing the matrices of the instances takes `O(ng) · O(nD)` steps, the third term
  (`steps_instances_mul_tWrites`).
* Reading the answers takes a constant number of steps for each of the at most `n²/√D` query pairs
  of an instance (`steps_tAnswers`).  This is the term `C n²/√D` beside the time of the solver.
* There are at most `F(p) + 1 = O(κ n³ log n/√D)` scans, where `F(p)` is the number of false
  positives of the chosen prime, of `O(√D/g)` steps each: the first term
  (`steps_falsePositiveBound`, `steps_tScanCall`, `steps_scans`).

The sum is `steps_hostRest`, and `obeysBound17_hostTime` puts it into the form of `bound17`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The scans -/

/-- One scan looks at the `⌈s/g⌉ ≤ 2√D/g` vertices of a piece, where `s = ⌊√D⌋`, so it takes
`O(√D/g)` steps. -/
private theorem steps_tScanCall :
    Steps (fun θ => tScanCall (pieceSizeNat θ.D θ.g)) fun θ => Real.sqrt θ.D / θ.g := by
  have hone : ∀ θ : CostParams, θ.Hyp → 1 ≤ Real.sqrt θ.D / θ.g := fun θ hθ =>
    (one_le_div hθ.g_pos).2 hθ.hgD
  have hpiece : Steps (fun θ => pieceSizeNat θ.D θ.g) fun θ => Real.sqrt θ.D / θ.g := by
    refine Dominated.of_le_const_mul (C := 2) (by norm_num) fun θ hθ => ?_
    have hlt : (pieceSizeNat θ.D θ.g : ℝ) * θ.g < (Nat.sqrt θ.D : ℝ) + θ.g := by
      exact_mod_cast Nat.ceilDiv_mul_lt (a := Nat.sqrt θ.D) hθ.hg
    rw [← mul_div_assoc, le_div_iff₀ hθ.g_pos]
    -- `⌈s/g⌉ g < s + g ≤ √D + √D`.
    linarith [hlt, Real.nat_sqrt_le_real_sqrt (a := θ.D), hθ.hgD]
  exact (hpiece.const_mul.add (.const hone)).add (.const hone)

/-- The exponent that the host's bound on the false positives uses is at most `κ`. -/
private theorem kappaOf_le_of_hyp {θ : CostParams} (hθ : θ.Hyp) : kappaOf θ.n θ.U ≤ θ.κ := by
  rcases Nat.eq_zero_or_pos θ.U with hU | hU
  · simp [kappaOf, hU, hθ.hκ]
  · exact kappaOf_le ((by norm_num : 2 ≤ 16).trans hθ.sixteen_le_n) hU hθ.hκ hθ.hUn

/-- Proof of Theorem 17: there are at most `F(p) + 1 = O(κ n³ log n/√D)` scans, where `F(p)` is the
number of false positives of the chosen prime `p`.  The host bounds it by `falsePositiveBound`. -/
private theorem steps_falsePositiveBound :
    Steps (fun θ => falsePositiveBound θ.n θ.U θ.D + 1) fun θ =>
      θ.κ * (θ.n : ℝ) ^ 3 * Real.log θ.n / Real.sqrt θ.D := by
  have hconst : 0 ≤ Hashing.falsePositiveConst :=
    zero_le_one.trans Hashing.one_le_falsePositiveConst
  refine Steps.add ?_ (.const fun θ hθ => ?_)
  · -- `falsePositiveBound` is the constant of the false positives times `κ' n³ log n/√D`, rounded
    -- down, where `κ' = kappaOf n U ≤ κ`.
    refine Dominated.of_le_const_mul hconst fun θ hθ => (Nat.floor_le ?_).trans ?_
    · have hκ' : 0 ≤ kappaOf θ.n θ.U := zero_le_one.trans (one_le_kappaOf θ.n θ.U)
      positivity
    · gcongr
      exact kappaOf_le_of_hyp hθ
  · rw [one_le_div hθ.sqrt_pos]
    calc Real.sqrt θ.D ≤ mon 1 0 0 θ := by simpa [mon_eq] using hθ.sqrt_le_n
      _ ≤ mon 3 0 1 θ := Scale.mon_le_mon (by decide) hθ
      _ = θ.κ * (θ.n : ℝ) ^ 3 * Real.log θ.n := by
          rw [mon_eq]
          ring

/-- **The scans**: `O(√D/g) · O(κ n³ log n/√D)` is within the first term of the bound. -/
private theorem steps_scans :
    Steps (fun θ => tScanCall (pieceSizeNat θ.D θ.g) * (falsePositiveBound θ.n θ.U θ.D + 1))
      budget := by
  refine (steps_tScanCall.mul steps_falsePositiveBound).mono_right fun θ hθ =>
    le_trans (le_of_eq ?_) (termScans_le_budget θ)
  have hr : 0 < Real.sqrt θ.D := hθ.sqrt_pos
  have hg : (0 : ℝ) < θ.g := hθ.g_pos
  unfold termScans
  field_simp

/-! ## What is done for each instance -/

/-- The bound `4ng` on the number of instances is `O(ng)`. -/
private theorem steps_instances : Steps (fun θ => 4 * θ.n * θ.g) fun θ => (θ.n : ℝ) * θ.g :=
  (Steps.const_mul (Dominated.refl _ _)).mul (Dominated.refl _ _)

/-- Writing the two matrices of an instance takes `O(nD)` steps. -/
private theorem steps_tWrites :
    StepsMon (fun θ => tWrites θ.n θ.D (pieceSizeNat θ.D θ.g)) 1 2 0 := by
  unfold tWrites
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_tWriteX
              | apply steps_tWriteY
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_tWriteX
                            | apply steps_tWriteY
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_tWriteX
                      | apply steps_tWriteY
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_tWriteX
              | apply steps_tWriteY
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- Writing the matrices of all instances, `O(ng) · O(nD)`, is within the third term of the bound.
-/
private theorem steps_instances_mul_tWrites :
    Steps (fun θ => 4 * θ.n * θ.g * tWrites θ.n θ.D (pieceSizeNat θ.D θ.g)) budget :=
  (steps_instances.mul (steps_of_softO steps_tWrites)).mono_right fun θ hθ =>
    le_trans (le_of_eq (by
      simp only [termBuild, mon_eq, pow_zero, mul_one, pow_one, Real.sq_sqrt θ.D.cast_nonneg]
      ring)) (termBuild_le_budget hθ)

/-- Reading the answers of one instance takes `O(n²/√D)` steps, a constant number for each query
pair. -/
private theorem steps_tAnswers :
    Steps (fun θ => tAnswers (queryCapNat θ.n θ.D)) fun θ => (θ.n : ℝ) ^ 2 / Real.sqrt θ.D := by
  refine Steps.add (Steps.const_mul (Dominated.of_le fun θ hθ => cast_queryCapNat_le hθ))
    (.const fun θ hθ => ?_)
  rw [one_le_div hθ.sqrt_pos]
  exact hθ.sqrt_le_n.trans (le_self_pow₀ hθ.one_le_n two_ne_zero)

/-! ## The sum -/






private theorem supTime_zero (n D cap : ℕ) : supTime (fun _ => 0) n D cap = 0 := by
  simp [supTime]

/-- Under the hypotheses of Theorem 17 the host does not fall back on the brute force. -/
private theorem not_smallCase_of_hyp {θ : CostParams} (hθ : θ.Hyp) : ¬ SmallCase θ.n θ.D θ.g := by
  have hg : θ.g ≤ Nat.sqrt θ.D := by
    rw [Nat.le_sqrt']
    exact_mod_cast (Real.le_sqrt θ.g.cast_nonneg θ.D.cast_nonneg).1 hθ.hgD
  have hD16 := hθ.hD16
  have hDn := hθ.hDn
  have hg1 := hθ.hg
  unfold SmallCase
  omega

/-- The time of the host is the time of `4ng` calls of the solver plus the rest. -/
private theorem hostTime_eq {θ : CostParams} (hθ : θ.Hyp) {Dfun Gfun : ℕ → ℕ} (tD tG : ℕ → ℕ)
    (Tn : List ℕ → ℕ) (hD : Dfun θ.n = θ.D) (hG : Gfun θ.D = θ.g) :
    hostTime Dfun Gfun tD tG Tn θ.n θ.U
      = 4 * θ.n * θ.g * supTime Tn θ.n θ.D (queryCapNat θ.n θ.D) + hostRest tD tG θ := by
  rw [hostTime, hD, hG, if_neg (not_smallCase_of_hyp hθ), hostRest, hostMain, hostMain,
    hostLoopBound, hostLoopBound, supTime_zero]
  ring






/-- What is within the three terms is within `restBound`. -/
private theorem Steps.toRest {t : CostParams → ℕ} (h : Steps t budget) : Steps t restBound :=
  h.mono_right fun θ _ => le_add_of_nonneg_left (by positivity)

/-- The parameters, the square root of `D` and the tests at the beginning are within the bound, if
the routines that compute `D` and `g` are. -/
private theorem steps_hostSetup {tD tG : ℕ → ℕ} (hD : Steps (fun θ => tD θ.n) budget)
    (hG : Steps (fun θ => tG θ.D) budget) : Steps (fun θ => hostSetup tD tG θ.n θ.D) budget :=
  hD.add hG
  |>.add (by first
             |
               ((apply ThreeSumApsp.Scale.SoftO.mono);
                 (·
                     repeat'
                       with_reducible
                         first
                         | exact ThreeSumApsp.Scale.SoftO.const _
                         | apply steps_sqrt
                         | apply ThreeSumApsp.Scale.SoftO.add
                         | apply ThreeSumApsp.Scale.SoftO.mul
                         | apply ThreeSumApsp.Scale.SoftO.pow
                         | apply ThreeSumApsp.Scale.SoftO.max
                         | apply ThreeSumApsp.Scale.SoftO.sub
                         | apply ThreeSumApsp.Scale.SoftO.div);
                 (·
                     first
                     | decide
                     | exact isEmptyElim))
             |
               ((fail_if_success
                     (fail_if_success
                         ((apply ThreeSumApsp.Scale.SoftO.mono);
                           (on_goal 1 =>
                               ((repeat'
                                     with_reducible
                                       first
                                       | exact ThreeSumApsp.Scale.SoftO.const _
                                       | apply steps_sqrt
                                       | apply ThreeSumApsp.Scale.SoftO.add
                                       | apply ThreeSumApsp.Scale.SoftO.mul
                                       | apply ThreeSumApsp.Scale.SoftO.pow
                                       | apply ThreeSumApsp.Scale.SoftO.max
                                       | apply ThreeSumApsp.Scale.SoftO.sub
                                       | apply ThreeSumApsp.Scale.SoftO.div);
                                 (done))))));
                 (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
                 (all_goals
                     try
                       ((apply ThreeSumApsp.Scale.SoftO.mono);
                         (·
                             repeat'
                               with_reducible
                                 first
                                 | exact ThreeSumApsp.Scale.SoftO.const _
                                 | apply steps_sqrt
                                 | apply ThreeSumApsp.Scale.SoftO.add
                                 | apply ThreeSumApsp.Scale.SoftO.mul
                                 | apply ThreeSumApsp.Scale.SoftO.pow
                                 | apply ThreeSumApsp.Scale.SoftO.max
                                 | apply ThreeSumApsp.Scale.SoftO.sub
                                 | apply ThreeSumApsp.Scale.SoftO.div);
                         (· decide))))
             |
               ((apply ThreeSumApsp.Scale.SoftO.mono);
                 (·
                     repeat'
                       with_reducible
                         first
                         | exact ThreeSumApsp.Scale.SoftO.const _
                         | apply steps_sqrt
                         | apply ThreeSumApsp.Scale.SoftO.add
                         | apply ThreeSumApsp.Scale.SoftO.mul
                         | apply ThreeSumApsp.Scale.SoftO.pow
                         | apply ThreeSumApsp.Scale.SoftO.max
                         | apply ThreeSumApsp.Scale.SoftO.sub
                         | apply ThreeSumApsp.Scale.SoftO.div)) : StepsMon _ 0 1 0).withinBuild
  |>.add (Scale.SoftO.const _).withinBuild

/-- The loop over the instances, without the calls of the solver, is within the bound: writing the
matrices, no time for the solver, reading the answers, and the scans. -/
private theorem steps_hostLoopBound :
    Steps (fun θ => hostLoopBound (fun _ => 0) θ.n θ.U θ.D θ.g) restBound :=
  steps_instances_mul_tWrites.toRest
  |>.mul_add ((Scale.SoftO.const 0).withinBuild.toRest.mono_left fun θ _ => by
    rw [supTime_zero, Nat.mul_zero])
  |>.mul_add ((steps_instances.mul steps_tAnswers).mono_right fun _ hθ =>
    le_add_of_nonneg_right (budget_nonneg hθ))
  |>.add steps_scans.toRest
  |>.add (Scale.SoftO.const _).withinBuild.toRest

/-- **Everything but the calls of the solver** is within the bound, if the routines that compute `D`
and `g` are.  The summands stand in the order of `hostMain`. -/
private theorem steps_hostRest {tD tG : ℕ → ℕ} (hD : Steps (fun θ => tD θ.n) budget)
    (hG : Steps (fun θ => tG θ.D) budget) : Steps (hostRest tD tG) restBound :=
  (steps_hostSetup hD hG).toRest.add <|
    steps_chooseTime.toRest
    |>.add steps_tQueryCapNat.withinBuild.toRest
    |>.add steps_tCeilDiv_piece.withinBuild.toRest
    |>.add steps_tCeilDiv_num.withinBuild.toRest
    |>.add steps_tBitLen.withinScans.toRest
    |>.add steps_tDblTable.withinScans.toRest
    |>.add ((Scale.SoftO.const _).mul steps_tResidues).withinScans.toRest
    |>.add steps_tClasses.withinBuild.toRest
    |>.add steps_tChunks.withinBuild.toRest
    |>.add steps_hostLoopBound
    |>.add (Scale.SoftO.const _).withinBuild.toRest

/-- A bound `T` on the time of the solver that is monotone in the number of query pairs bounds its
largest time on the instances of the host. -/
private theorem cast_supTime_le {Tn : List ℕ → ℕ} {T : ℕ → ℕ → ℕ → ℝ}
    (hT : ∀ n D w w' : ℕ, 1 ≤ n → 1 ≤ D → w ≤ w' → (Tn [n, D, w] : ℝ) ≤ T n D w') {n D : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D) (cap : ℕ) : ((supTime Tn n D cap : ℕ) : ℝ) ≤ T n D cap := by
  obtain ⟨w, hw, hsup⟩ : ∃ w ∈ Finset.range (cap + 1),
      (Finset.range (cap + 1)).sup (fun w => Tn [n, D, w]) = Tn [n, D, w] :=
    Finset.exists_mem_eq_sup _ ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ _
  rw [supTime, hsup]
  exact hT n D w cap hn hD (Nat.lt_succ_iff.1 (Finset.mem_range.1 hw))

/-- **The bound of Theorem 17 for the host.**  The parameter routines compute `Dfun n` from `n` and
`Gfun D` from `D`.  These agree with the parameters `D n` and `g n` of the claim, which are defined
with real powers, and the routines run within the bound. -/
theorem obeysBound17_hostTime_sourceProof (D g : ℕ → ℕ) {Dfun Gfun tD tG : ℕ → ℕ} (hDf : ∀ n, Dfun n = D n)
    (hGf : ∀ n, 1 ≤ n → Gfun (D n) = g n) (hD : Steps (fun θ => tD θ.n) budget)
    (hG : Steps (fun θ => tG θ.D) budget) :
    ObeysBound17 strassen D g (hostTime Dfun Gfun tD tG) := by
  obtain ⟨C, hC, hsteps⟩ := steps_hostRest hD hG
  refine ⟨C, hC, fun Tn T hT n U κ h16 hDn hg1 hg hκ hU => ?_⟩
  have hθ : CostParams.Hyp ⟨n, D n, g n, U, κ⟩ := ⟨h16, hDn, hg1, hg, hκ, hU⟩
  have hn1 : 1 ≤ n := hθ.one_le_n_nat
  have hD1 : 1 ≤ D n := hθ.one_le_D_nat
  have hsolver := cast_supTime_le hT hn1 hD1 (queryCapNat n (D n))
  have hrest : (hostRest tD tG ⟨n, D n, g n, U, κ⟩ : ℝ)
      ≤ C * ((n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n)) + budget ⟨n, D n, g n, U, κ⟩) :=
    hsteps _ hθ
  have hquery : 0 ≤ C * ((n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n))) := by positivity
  rw [hostTime_eq hθ tD tG Tn (hDf n) (hGf n hn1)]
  rw [queryCapNat_eq n hD1] at hsolver ⊢
  push_cast
  -- The calls cost `4ng T`; in the rest, `C ng · n²/√D ≤ 4ng · C n²/√D`.
  calc 4 * (n : ℝ) * g n * (supTime Tn n (D n) (queryCap n (D n)) : ℝ)
        + (hostRest tD tG ⟨n, D n, g n, U, κ⟩ : ℝ)
      ≤ 4 * (n : ℝ) * g n * T n (D n) (queryCap n (D n))
        + C * ((n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n)) + budget ⟨n, D n, g n, U, κ⟩) := by
        gcongr
    _ ≤ bound17 strassen D g C T n κ := by
        unfold bound17 budget
        linarith [hquery]

end Light.Sec3

end
end


theorem solution : ∀ (D g : Nat → Nat) {Dfun Gfun tD tG : Nat → Nat},
  (∀ (n : Nat), @Eq.{1} Nat (Dfun n) (D n)) →
    (∀ (n : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
          @Eq.{1} Nat (Gfun (D n)) (g n)) →
      Light.Sec3.Steps (fun (θ : Light.Sec3.CostParams) => tD θ.n) Light.Sec3.budget →
        Light.Sec3.Steps (fun (θ : Light.Sec3.CostParams) => tG θ.D) Light.Sec3.budget →
          Light.Sec3.ObeysBound17 ThreeSumApsp.strassen D g (Light.Sec3.hostTime Dfun Gfun tD tG) := by
  exact @Light.Sec3.obeysBound17_hostTime_sourceProof

#print axioms solution

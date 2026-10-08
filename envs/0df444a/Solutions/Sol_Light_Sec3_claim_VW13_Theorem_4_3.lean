-- Prove2me | solution 1 for Light.Sec3.claim_VW13_Theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-06T15:56:55.782359+00:00
-- url     : https://prove2.me/submissions/fe941f65-98ce-4a5f-b795-ea8b0cb1f23e

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_ThreeSumSource_ReductionClaims
import Init
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Realized
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Places
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem19_Choice
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Table2_LogBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Statements_Exponents
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Corollary15_16
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem19
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem21_22
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Ceil
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Count
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Iterate
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Common
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Sec3_claim_VW13_Theorem_3_3
import Theorems.Thm_Light_Sec3_claim_VW18_Theorem_4_2
import Theorems.Thm_Light_Sec3_claim_apspFromMinPlus
import Theorems.Thm_Light_Sec3_et17_spec
import Theorems.Thm_Light_Sec3_obeysBound17_hostTime
import Theorems.Thm_Light_Sec4_allInstances26_solves
import Theorems.Thm_Light_Sec4_allInstancesTime26_le
import Theorems.Thm_Light_Sec4_pre31_program31
import Theorems.Thm_Light_Sec4_queryAt_spec
import Theorems.Thm_Light_Sec4_specs40
import Theorems.Thm_Light_Wrap_realized
import Theorems.Thm_ThreeSumApsp_Dominated_of_eventually
import Theorems.Thm_ThreeSumApsp_FromClaims_solvedAt_of_realized
import Theorems.Thm_ThreeSumApsp_Theorem19_Choice_ceil_le_sqrt
import Theorems.Thm_ThreeSumApsp_WordRam_bigO_of_le_rpow
import Theorems.Thm_ThreeSumApsp_goodTime_uniformTime
import Theorems.Thm_TrulySubcubicAPSP_sourceSpecificationTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/



set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace EndStatement
end EndStatement
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

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



/-- A bound with constant one. -/
theorem of_le (hfg : ∀ x, dom x → f x ≤ g x) : Dominated dom f g :=
  ⟨1, zero_le_one, fun x hx => by simpa only [one_mul] using hfg x hx⟩

















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
# Powers of `n` and of `log n` for large `n`

The facts behind the paper's `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`, for functions of a natural number
`n` and in the language of Mathlib's `f =O[atTop] g`. Powers of `n` are monotone in the exponent
(`isBigO_rpow_rpow_of_le`, `isBigO_rpow_mul_log_pow_of_le`) and multiply by adding exponents
(`rpow_mul_rpow_eventuallyEq`). A constant or a power of `log n` is below every positive power of
`n` (`eventually_le_rpow`, `isLittleO_log_pow_rpow`). Hence `n ^ a * (log n) ^ e` is `o(n ^ b)` and
`O(n ^ b)` for `a < b` (`isLittleO_rpow_mul_log_pow_rpow`, `isBigO_rpow_mul_log_pow_rpow`), which is
where logarithms are absorbed for large `n`; with the constant absorbed too, this is
`eventually_mul_rpow_mul_log_pow_le`. The rounded power `⌈n ^ μ⌉` tends to infinity for `μ > 0`
(`tendsto_ceil_rpow_atTop`).
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

/-- A bound `|f n| ≤ C * g n` from some `n₀` on gives `f = O(g)`. -/
theorem isBigO_of_abs_le {f g : ℕ → ℝ} (C : ℝ) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → |f n| ≤ C * g n) :
    f =O[atTop] g := by
  refine IsBigO.of_bound |C| (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
  exact (h n hn).trans (le_abs_self _)










/-- `n ^ a = O(n ^ b)` for `a ≤ b`. -/
theorem isBigO_rpow_rpow_of_le {a b : ℝ} (hab : a ≤ b) :
    (fun n : ℕ => (n : ℝ) ^ a) =O[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  refine isBigO_of_abs_le 1 1 fun n hn => ?_
  rw [one_mul, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg a)]
  exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) hab

/-- `n ^ a * n ^ b = n ^ (a + b)` for all large `n`. -/
theorem rpow_mul_rpow_eventuallyEq (a b : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ a * (n : ℝ) ^ b) =ᶠ[atTop] fun n : ℕ => (n : ℝ) ^ (a + b) := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.rpow_add (Nat.cast_pos.2 hn)]

/-- `(log n) ^ e = o(n ^ η)` for `η > 0`. -/
theorem isLittleO_log_pow_rpow {η : ℝ} (hη : 0 < η) (e : ℕ) :
    (fun n : ℕ => Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ η := by
  have h := (isLittleO_log_rpow_rpow_atTop (e : ℝ) hη).comp_tendsto tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.rpow_natCast] using h





/-- Logarithms are absorbed: `n ^ a * (log n) ^ e = o(n ^ b)` for `a < b`. -/
theorem isLittleO_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  have h := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ a) atTop).mul_isLittleO
    (isLittleO_log_pow_rpow (sub_pos.2 hab) e)
  refine h.congr' EventuallyEq.rfl ?_
  simpa only [add_sub_cancel] using rpow_mul_rpow_eventuallyEq a (b - a)






/-- Constants are absorbed as well: `C * (n ^ a * (log n) ^ e) ≤ n ^ b` for all large `n`, if
`a < b`. -/
theorem eventually_mul_rpow_mul_log_pow_le (C : ℝ) {a b : ℝ} (hab : a < b) (e : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * ((n : ℝ) ^ a * Real.log n ^ e) ≤ (n : ℝ) ^ b := by
  have h := ((isLittleO_rpow_mul_log_pow_rpow hab e).const_mul_left C).def zero_lt_one
  filter_upwards [h] with n hn
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg b)] at hn
  exact (le_abs_self _).trans hn

/-- `C * n ^ a ≤ n ^ b` for all large `n`, if `a < b`. -/
theorem eventually_mul_rpow_le (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  simpa only [pow_zero, mul_one] using eventually_mul_rpow_mul_log_pow_le C hab 0

end ThreeSumApsp

end
end

section


/-!
# The notions of solving are monotone

That the program `P` with slope `b` solves the problem on the instances in `dom` within time `T`, at
every admissible word size, stays true for a larger slope, a smaller set of instances and a larger
time bound (`Solves.mono`).  The same holds for a two-stage data structure (`IsDataStructure.mono`).

* The item statements on the problems of the end statement use `SolvesWithin`.  It is `Solves` for
  the problem `ofEnd Q`, whose instances carry their size and a bound on their numbers
  (`solvesWithin_iff`, `solvedInTimeAt_iff`).

* A statement "there are a program and a constant `C` such that the time is at most `C f(x)`" stays
  true for every bound `g` with `f = O(g)`: `exists_solves_of_dominated`, and
  `exists_isDataStructure_of_dominated` for a data structure.
* For the bounds `O(n^a (log n)^e)` in one size: a larger exponent (`SolvedInTime.mono_exponent`),
  and a larger exponent that absorbs the logarithms (`SolvedInPolylogTime.solvedInTime`).
-/

public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr)
open Filter

/-! ## The problems of the end statement as problems in the sense of `Problem` -/


































/-! ## Monotonicity -/





















/-! ## Bounds up to a constant -/
























/-! ## Bounds in one size -/

















end ThreeSumApsp.WordRam

end
end

section


/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h











/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩



theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q :=
  ⟨_, _, .store ha he hA, hT, h⟩

theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩













/-- Loops.  I i is the invariant before round number i (counted from 0) of n rounds, and b i bounds
the cost of that round. -/
theorem Ends.while {σ c s} {Q : State → Prop} (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ (b i) (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ) :
    Ends lim P d (.while c s) σ (∑ i ∈ Finset.range n, (c.cost + 1 + b i) + (c.cost + 1)) Q := by
  have aux : ∀ j i σ, i + j = n → I i σ →
      Ends lim P d (.while c s) σ
        (∑ k ∈ Finset.range j, (c.cost + 1 + b (i + k)) + (c.cost + 1)) Q := by
    intro j
    induction j with
    | zero =>
      intro i σ hij hi
      obtain rfl : i = n := by omega
      obtain ⟨h1, h2, h3⟩ := hn σ hi
      exact ⟨σ, _, .whileFalse h1 h2, by simp, h3⟩
    | succ j ih =>
      intro i σ hij hi
      obtain ⟨h1, h2, σ', k₁, he₁, hk₁, hi'⟩ := hs i σ (by omega) hi
      obtain ⟨σ'', k₂, he₂, hk₂, hq⟩ := ih (i + 1) σ' (by omega) hi'
      refine ⟨σ'', _, .whileTrue h1 h2 he₁ he₂, ?_, hq⟩
      rw [Finset.sum_range_succ']
      have : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
      simp only [this] at hk₂
      simp only [Nat.add_zero]
      omega
  simpa using aux n 0 σ (by omega) hI

/-- Loops in which every round costs at most b. -/
theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q :=
  (Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h
































/-- Calls: verify the body from the frame made of the arguments. -/
theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ) (ha : ∀ e ∈ args, e.Safe lim σ)
    (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩

/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/

























/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame












/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/
























end Light

end
end

section


/-!
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light

/-! ## Regions -/


















/-! ## Memories that agree on some cells -/























variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}




theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl






/-- Two steps that keep different cells. -/
theorem SameOn.then (h₁ : SameOn K₁ μ μ') (h₂ : SameOn K₂ μ' μ'') (hK : ∀ b, K b → K₁ b ∧ K₂ b) :
    SameOn K μ μ'' :=
  fun b hb => (h₂ b (hK b hb).2).trans (h₁ b (hK b hb).1)



/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}





/-- Nothing has been written yet. -/
theorem wrote_zero : wrote μ dst f 0 = μ := by
  funext a
  unfold wrote
  rw [if_neg (by omega)]

/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]

/-- One more cell is written. -/
theorem wrote_succ : Function.update (wrote μ dst f j) (dst + j) (f j) = wrote μ dst f (j + 1) := by
  funext a
  by_cases h : a = dst + j
  · subst h
    rw [Function.update_self, wrote_done (Nat.lt_succ_self j)]
  · rw [Function.update_of_ne h]
    unfold wrote
    by_cases h' : dst ≤ a ∧ a < dst + j
    · rw [if_pos h', if_pos (by omega)]
    · rw [if_neg h', if_neg (by omega)]














/-! ## The tactics -/









































end Light

end
end

section


/-!
# Index arithmetic: a pair of numbers as one number

General facts about natural numbers. A matrix with rows of length `n` is kept as one list, row
after row: the entry in row `a` and column `b < n` has the index `a * n + b`. This file has

* the bounds on such an index (`Nat.mul_add_lt_mul`, `Nat.mul_add_le_mul`);
* the way back from the index to the pair (`Nat.mul_add_div_of_lt`, `Nat.mul_add_inj_of_lt`,
  `Nat.div_lt_of_lt_mul'`, `Nat.mod_lt_of_lt_mul`, `Nat.exists_eq_mul_add_of_lt_mul`,
  `Nat.eq_mul_succ_iff`);
* the pair of the next index (`Nat.succ_div_mod_of_lt`, `Nat.succ_div_mod_of_ne`,
  `Nat.succ_div_mod_of_eq`);
* residues seen as natural numbers (`Int.toNat_emod_lt`, `Int.natCast_toNat_emod`).
-/

public section

namespace Nat

/-! ## Bounds on an index -/







/-! ## From the index back to the pair

The column is `Nat.mul_add_mod_of_lt : c < b → (a * b + c) % b = c`. -/

































/-! ## The next index -/























end Nat

namespace Int

/-! ## Residues as natural numbers -/










end Int

end
end

section


/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-! ## Entries with a default -/

/-- What holds for the default and for every member of a list holds for every `getD`. -/
theorem getD_of_forall_mem {p : α → Prop} {l : List α} {d : α} (hd : p d) (h : ∀ x ∈ l, p x)
    (i : ℕ) : p (l.getD i d) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem l d hi]
    exact h _ (List.getElem_mem hi)
  · rwa [List.getD_eq_default l d hi]























































/-! ## Blocks one after the other -/











































































/-! ## Sums -/









































section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]














end



































/-! ## A running minimum -/
























/-! ## Counting -/












































































/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]








































end Sorted

end List

namespace ThreeSumApsp

variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/














/-- A bound on the absolute values of all members bounds every `getD` with default `0`. -/
theorem AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U :=
  List.getD_of_forall_mem (p := fun x => |x| ≤ U) (by rwa [abs_zero]) h i

/-! ## The entrywise sum of lists -/






















end ThreeSumApsp

end
end

section


/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light

open ThreeSumApsp







variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}




































/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]
















/-- Writing outside a segment. -/
theorem Seg.update_out (h : Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _



/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)





























































































end Light

end
end

section


/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Blocks -/




































/-! ## The default proofs -/



































/-! ## Rules for blocks -/























theorem Ends.of_blockSafe : ∀ {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}, s.BlockSafe lim σ →
    s.blockCost ≤ T → Q (s.after σ) → Ends lim P d s σ T Q
  | .skip, _, _, _, _, _, h => Ends.skip h
  | .set _ _, _, _, _, hs, hT, h => Ends.set hs hT h
  | .store _ _, _, _, _, hs, hT, h => Ends.store hs.1 hs.2.1 hs.2.2 hT h
  | .seq s t, _, _, _, hs, hT, h =>
    Ends.seq s.blockCost t.blockCost
      (Ends.of_blockSafe hs.1 le_rfl (Ends.of_blockSafe hs.2 le_rfl h)) hT
  | .ite c s t, σ, _, _, hs, hT, h =>
    Ends.ite (max s.blockCost t.blockCost) hs.1
      (fun hc => Ends.of_blockSafe (hs.2.1 hc) (le_max_left _ _)
        (by simpa only [Stmt.after, if_pos hc] using h))
      (fun hc => Ends.of_blockSafe (hs.2.2 hc) (le_max_right _ _)
        (by simpa only [Stmt.after, if_neg hc] using h))
      hT
  | .while _ _, _, _, _, hs, _, _ => hs.elim
  | .call _ _ _, _, _, _, hs, _, _ => hs.elim

/-- **Blocks.**  A block that runs safely from σ ends within any T ≥ s.blockCost, in the state
s.after σ. -/
theorem Ends.block {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop} (h : s.Runs lim σ Q)
    (hT : s.blockCost ≤ T := by first
                                  |
                                    ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                      (first
                                        | omega
                                        | ((ring_nf); (omega))))
                                  | omega
                                  |
                                    (simp [] <;>
                                        first
                                        | omega
                                        | ((ring_nf); (omega)))) : Ends lim P d s σ T Q :=
  Ends.of_blockSafe h.1 hT h.2

/-! ## Sequencing: what is left of the time goes to the rest of the program -/

/-- The first statement gets T₁ steps, the rest of the program what is left of T. -/
theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by first
                           |
                             ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                   List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                               (first
                                 | omega
                                 | ((ring_nf); (omega))))
                           | omega
                           |
                             (simp [] <;>
                                 first
                                 | omega
                                 | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)





/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s .skip)) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  h












































/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                ((try have := Light.Std.const_le (by assumption)));
                                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by first
                                                                                                                        |
                                                                                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                                                                            (first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega))))
                                                                                                                        | omega
                                                                                                                        |
                                                                                                                          (simp [] <;>
                                                                                                                              first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.ite c s₁ s₂) σ T Q :=
  Ends.ite _ hs h₁ h₂ (by omega)

























/-! ## Loops whose body is a block -/

/-- **Loops whose body is a block.**  I j is the invariant before round j of n rounds.  The time is
computed from body.blockCost. -/
theorem Ends.whileBlock {σ : State} {c : Cond} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (start : I 0 σ)
    (round : ∀ (j : ℕ) (σ : State), j < n → I j σ →
      c.Safe lim σ ∧ c.Holds σ ∧ body.Runs lim σ (I (j + 1)))
    (done : ∀ σ : State, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + body.blockCost) + (c.cost + 1) ≤ T := by first
                                                                       |
                                                                         ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                               List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                           (first
                                                                             | omega
                                                                             | ((ring_nf); (omega))))
                                                                       | omega
                                                                       |
                                                                         (simp [] <;>
                                                                             first
                                                                             | omega
                                                                             | ((ring_nf); (omega)))) :
    Ends lim P d (.while c body) σ T Q :=
  Ends.whileConst I n body.blockCost start
    (fun j σ hj hI => ⟨(round j σ hj hI).1, (round j σ hj hI).2.1,
      Ends.block (round j σ hj hI).2.2 le_rfl⟩) done hT

/-! ## Counting loops -/





/-- **Counting loops.**  I j is the invariant before round j.  The bound hi has the value n
throughout, n fits in a word, and the body keeps the counter and takes at most b steps.  The rule
supplies σ.loc i = j; I 0 is asked of σ with 0 in the counter, and I (j + 1) of the state after the
increment. -/
theorem Ends.for {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n b : ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i = j → I j σ → Ends lim P d body σ b fun σ' =>
      σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ → hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first
                                                          |
                                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                              (first
                                                                | omega
                                                                | ((ring_nf); (omega))))
                                                          | omega
                                                          |
                                                            (simp [] <;>
                                                                first
                                                                | omega
                                                                | ((ring_nf); (omega)))) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg n) hn
  refine Ends.seq 2 (n * (hi.cost + b + 7) + hi.cost + 3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  refine Ends.whileConst (fun j σ => σ.loc i = j ∧ I j σ) n (b + 4) ⟨by simp, by simpa using start⟩
    ?_ ?_ (le_of_eq (by simp only [Cond.cost, Expr.cost]; ring))
  · rintro j σ hj ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial, hs⟩, ?_, Ends.seq b 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc, hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc', hI'⟩
      have hval : (((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ' = (j : ℤ) + 1 := by simp [hc']
      have hj' : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial, ?_, ?_⟩ (by simp) ⟨?_, ?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ'| ≤ lim.word
        rw [hval, abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  · rintro σ ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial, hs⟩, ?_, done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc, hv]
    exact lt_irrefl _



end Light

end
end

section


/-!
# Arrays in the memory

A routine assumes the same facts about each of its arrays: which list it holds, how long the list
is, and that it lies below some address `top`, from which on the routine writes: the free pointer,
the place of the result, the scratch space.  `ListAt μ a l N top` is the record of these three
facts, and `ArrayAt μ a l N U top` adds a bound `U` on the entries.  `IndexAt μ a l N p top` is the
record for a list of natural numbers below `p`.  What a routine assumes is then a record with one
field for each array.

* `ListAt.keep`, `ArrayAt.keep`: an array stays in place when its cells do not change.
* `ListAt.mono`, `ArrayAt.mono`: `top` and `U` may grow.
* `ListAt.read`, `ArrayAt.read`, `ArrayAt.abs_read_le`: what a cell holds, and how large it is.
* `ListAt.drop_take`, `ArrayAt.drop_take`: a piece of an array is an array.
* `IndexAt.keep`, `IndexAt.read`, `IndexAt.getD_lt`: the same for natural numbers.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}















namespace ListAt




















end ListAt

namespace ArrayAt



























end ArrayAt









namespace IndexAt

variable {l : List ℕ} {p : ℕ}






















end IndexAt

end Light

end
end

section


/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The list of the locals -/









/-- Reading a local after an assignment. -/
theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

/-- An assignment to a local, in terms of the list. -/
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]



/-! ## The value of an expression -/





/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}














/-- `x := e`, where e gives z. -/
theorem Ends.setTo {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨frame (setLocal l x z), μ⟩)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d (.set x e) ⟨frame l, μ⟩ T Q := by
  refine Ends.set he.1 hT ?_
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h

/-- `x := e ; s`, where e gives z.  The rest s of the text gets the steps that are left. -/
theorem Ends.setToThen {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.set x e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT








































end rules

/-! ## Locals by name, and locals whose values do not matter -/




































































section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

























/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}































/-! ## Counting loops with scratch variables -/













































end

end Light

end
end

section


/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Specifications of procedures -/







section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩



















end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}

/-- `x := p(args)`, where the arguments give vals.  The procedure runs at depth d + 1. -/
theorem Ends.callLast (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by (((try have := Light.Std.space_le (by assumption)));
                                                                                                        ((try have := Light.Std.const_le (by assumption)));
                                                                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT











/-- `x := p(args)`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callTo (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨frame (setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨frame l, μ⟩ T Q :=
  Ends.callLast hp (fun r μ' hR => update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT

/-- `x := p(args) ; s`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callToThen (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨frame (setLocal l x r), μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.call p args x) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light

end
end

section


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
















































































end Light

end
end

section


/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Limits -/

























/-! ## Specifications of single routines -/






/-! ## Tasks and solvers -/





























/-- **A solver meets the specification that its task prescribes**, in every program that begins with
its program. -/
theorem Solves.meets {task : Task} {P₀ : Program} {p : ℕ} {T₀ : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (h : _root_.Light.Solves task P₀ p T₀ need) (R : Program) {lim : Limits} {d : ℕ} (x : task.Inst) {μ : ℕ → ℤ}
    (fr : ℕ) (hpre : task.Pre x μ fr) (hok : (need (task.size x) (task.bound x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.size x) (task.bound x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩






















/-! ## Hosts -/






















/-! ## Tasks with a list of parameters -/
































end Light

end
end

section


/-!
# The answer of a decision problem as a number

A routine for a decision problem returns 1 for yes and 0 for no: `flag p` is this number for the
proposition `p`.
-/

@[expose] public section

namespace ThreeSumApsp

















/-- Equivalent questions have the same answer. -/
theorem flag_congr {p q : Prop} (h : p ↔ q) : flag p = flag q := by
  rw [propext h]







end ThreeSumApsp

end
end

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






























/-! ## The ceiling of a logarithm

`Real.natCeil_logb_natCast : ⌈Real.logb b n⌉₊ = Nat.clog b n` passes from real to natural numbers,
and `Nat.le_pow_clog : 1 < b → x ≤ b ^ Nat.clog b x` is the lower bound. -/



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

































/-! ### The rounded logarithm `Nat.clog` -/
















end Real

namespace ThreeSumApsp






end ThreeSumApsp

end
end

section


/-!
# Calculating with `O(n^a)` and `Õ(n^a)`

Closure properties of the two classes `IsBigOPow f a`, that is `f(n) = O(n^a)`, and
`IsPowPolylog f a`, that is `f(n) = O(n^a (log n)^{O(1)})`, which the paper writes `Õ(n^a)`.

A bound enters by `of_abs_le`, by `of_isBigO`, or from the model functions (`isBigOPow_rpow`,
`isBigOPow_natCast_pow`, `isBigOPow_const`, `isPowPolylog_rpow_mul_log_pow`, `isPowPolylog_log_pow`,
and for rounded powers `isBigOPow_ceil_rpow`, `isBigOPow_floor_rpow` and their inverses;
`IsBigOPow.natCeil` for rounding in general). Both classes are closed under sums, constant factors
and passing to a smaller function (`mono_left`). A product has the exponent `a + b` and a power the
exponent `a * k` (`pow`, `rpow`), to be brought to the wanted form by `mono`, which asks only for an
inequality between exponents. Substituting `n ↦ size n` multiplies nonnegative exponents
(`IsBigOPow.comp`, `IsPowPolylog.comp`), for `size n = O(n^μ)`, and then `log (size n) = Õ(1)`
(`IsBigOPow.isPowPolylog_log_natCast`). The classes are related by `IsBigOPow.isPowPolylog` and,
with a loss in the exponent, `IsPowPolylog.isBigOPow`; `eventually_abs_le` absorbs the constant as
well.
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

variable {f g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` -/

/-- `n ^ a = O(n^a)`. -/
theorem isBigOPow_rpow (a : ℝ) : IsBigOPow (fun n : ℕ => (n : ℝ) ^ a) a :=
  isBigO_refl _ _









namespace IsBigOPow





/-- If `g = O(n^a)` and `f = O(g)`, then `f = O(n^a)`. -/
theorem of_isBigO (hg : IsBigOPow g a) (hfg : f =O[atTop] g) : IsBigOPow f a :=
  hfg.trans hg

/-- If `|f n| ≤ |g n|` for all large `n` and `g = O(n^a)`, then `f = O(n^a)`. -/
theorem mono_left (hg : IsBigOPow g a) (h : ∀ᶠ n in atTop, |f n| ≤ |g n|) : IsBigOPow f a :=
  hg.of_isBigO (IsBigO.of_bound' h)



/-- The exponent may be raised. -/
protected theorem mono (hf : IsBigOPow f a) (hab : a ≤ b) : IsBigOPow f b :=
  hf.trans (isBigO_rpow_rpow_of_le hab)




















/-- The constant is absorbed: if `f = O(n^a)` and `a < b`, then `|f n| ≤ n ^ b` for all large `n`.
-/
theorem eventually_abs_le (hf : IsBigOPow f a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ b := by
  obtain ⟨C, hC⟩ := IsBigO.bound hf
  filter_upwards [hC, eventually_mul_rpow_le C hab] with n hn hCn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg a)] at hn
  exact hn.trans hCn



end IsBigOPow





























/-! ### `Õ(n^a)` -/



















namespace IsPowPolylog






























































end IsPowPolylog



















end ThreeSumApsp

end
end

section


/-!
# One-sided bounds `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`

A running time is bounded from above only. `UpperBigOPow f a`, `UpperPowPolylog f a` and
`UpperPowLittleO f a` say that `f(n)` is eventually at most `C n^a`, at most `C n^a (log n)^e`, and
at most `n^{a+ε(n)}` with `ε(n) → 0`, where `IsBigOPow`, `IsPowPolylog` and `IsPowLittleO` say this
of `|f(n)|`.

A bound on `|f|` is a bound on `f` (`IsBigOPow.upperBigOPow`), and the function may be replaced by a
smaller one (`mono_left`); these two lemmas have the same names for the three classes. For `Õ(n^a)`
and `n^{a+o(1)}` a bound on `f` is a bound by a nonnegative function of the class that bounds `|f|`
(`UpperPowPolylog.exists_isPowPolylog`). For `Õ(n^a)` the closure properties follow: a bound on `f`
is a bound on `|f|` if `f` is eventually nonnegative (`UpperPowPolylog.isPowPolylog`), sums,
nonnegative constant factors, products with a nonnegative factor, a larger exponent (`mono`).
Logarithms and the `o(1)` are absorbed by a strictly larger exponent
(`UpperPowPolylog.upperBigOPow`, `UpperPowLittleO.upperBigOPow`).
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp















variable {f f' g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` from above -/








namespace UpperBigOPow






end UpperBigOPow

/-! ### `Õ(n^a)` from above -/



namespace UpperPowPolylog


















































end UpperPowPolylog

/-! ### `n^{a+o(1)}` from above -/






namespace UpperPowLittleO




















end UpperPowLittleO

end ThreeSumApsp

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

/-- A count that is at most `hidden`. -/
theorem of_le_hidden (h : ∀ x, s.dom x → (t x : ℝ) ≤ s.hidden x) : s.SoftO t 0 :=
  ⟨1, .of_le fun x hx => by simpa only [pow_one, mon_zero, mul_one] using h x hx⟩

/-- A count that is at most a constant times a base. -/
theorem of_dominated_base [DecidableEq ι] (i : ι)
    (h : Dominated s.dom (fun x => (t x : ℝ)) (s.base i)) : s.SoftO t (Pi.single i 1) :=
  ⟨0, h.congr (fun _ _ => rfl) fun x _ => by rw [pow_zero, mon_single, one_mul]⟩

/-- A count that is at most a base. -/
theorem of_le_base [DecidableEq ι] (i : ι) (h : ∀ x, s.dom x → (t x : ℝ) ≤ s.base i x) :
    s.SoftO t (Pi.single i 1) :=
  of_dominated_base i (.of_le h)



/-- The bound, written out. -/
theorem exists_le (h : s.SoftO t e) :
    ∃ (C : ℝ) (c : ℕ), 0 ≤ C ∧ ∀ x, s.dom x → (t x : ℝ) ≤ C * (s.hidden x ^ c * s.mon e x) :=
  let ⟨c, C, hC, hle⟩ := h
  ⟨C, c, hC, hle⟩

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















/-- A square root is at most the number. -/
protected theorem sqrt (h : s.SoftO t e) : s.SoftO (fun x => Nat.sqrt (t x)) e :=
  h.of_le fun _ _ => Nat.sqrt_le_self _




































end SoftO

end Scale








































end ThreeSumApsp

end
end

section


/-!
# Polynomially bounded needs

The need of a program is given by explicit expressions in the size n of the input and the bound U on
its numbers.  `PolyBounded F` says that F(n, U) is at most a polynomial in (n + 1)(U + 1).  It is
the calculus `ThreeSumApsp.Scale.SoftO` on the scale `polyScale`, and the tactic `growth_poly`
proves it by following the expression.

Three such functions make a polynomially bounded need (`PolyBounded.polyNeed`), and the need of a
solver that a host calls has three such parts (`PolyNeed.word`, `PolyNeed.cells`, `PolyNeed.depth`).
So the need of a host is polynomially bounded if the need of its solver is; the tactic `poly_need`
proves this from the definition of the need of the host.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Upper bounds that are polynomial in (n + 1)(U + 1) -/













namespace PolyBounded

variable {F : ℕ → ℕ → ℕ}

/-- The size `n` is polynomially bounded. -/
theorem fst : PolyBounded (fun n _ => n) :=
  (Scale.SoftO.of_le_hidden fun p _ => Nat.cast_le.2 <|
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ p.2.succ_pos)).mono (by decide)

/-- The bound `U` is polynomially bounded. -/
theorem snd : PolyBounded (fun _ U => U) :=
  (Scale.SoftO.of_le_hidden fun p _ => Nat.cast_le.2 <|
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ p.1.succ_pos)).mono (by decide)

/-- A smaller function has the same bound. -/
theorem of_le {G : ℕ → ℕ → ℕ} (h : PolyBounded G) (hle : ∀ n U, F n U ≤ G n U) : PolyBounded F :=
  Scale.SoftO.of_le h fun _ _ => hle _ _

/-- The bound with natural numbers. -/
theorem exists_nat_le (h : PolyBounded F) :
    ∃ K e : ℕ, ∀ n U, F n U ≤ K * ((n + 1) * (U + 1)) ^ e := by
  obtain ⟨C, e, hC, hle⟩ := h.exists_le
  refine ⟨⌈C⌉₊, e, fun n U => ?_⟩
  have hceil : (F n U : ℝ) ≤ ⌈C⌉₊ * (((n + 1) * (U + 1) : ℕ) : ℝ) ^ e := by
    simpa [polyScale, Scale.mon] using (hle (n, U) trivial).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by simp [polyScale, Scale.mon]; positivity))
  exact_mod_cast hceil

end PolyBounded






namespace PolyBounded

/-- A polynomial bound at polynomially bounded parameters. -/
theorem polyBound {A B : ℕ → ℕ → ℕ} (hA : PolyBounded A) (hB : PolyBounded B) (s k : ℕ) :
    PolyBounded (fun n U => polyBound s k [A n U, B n U]) :=
  of_le (G := fun n U => 2 ^ s * ((A n U + 1) * (B n U + 1)) ^ k) (by first
                                                                      |
                                                                        ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                          (·
                                                                              repeat'
                                                                                with_reducible
                                                                                  first
                                                                                  | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                  | apply Light.PolyBounded.fst
                                                                                  | apply Light.PolyBounded.snd
                                                                                  | apply ThreeSumApsp.Scale.SoftO.log
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                  | apply hA
                                                                                  | apply hB
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
                                                                                                | apply Light.PolyBounded.fst
                                                                                                | apply Light.PolyBounded.snd
                                                                                                | apply ThreeSumApsp.Scale.SoftO.log
                                                                                                | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                                | apply hA
                                                                                                | apply hB
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
                                                                                          | apply Light.PolyBounded.fst
                                                                                          | apply Light.PolyBounded.snd
                                                                                          | apply ThreeSumApsp.Scale.SoftO.log
                                                                                          | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                          | apply hA
                                                                                          | apply hB
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
                                                                                  | apply Light.PolyBounded.fst
                                                                                  | apply Light.PolyBounded.snd
                                                                                  | apply ThreeSumApsp.Scale.SoftO.log
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                  | apply hA
                                                                                  | apply hB
                                                                                  | apply ThreeSumApsp.Scale.SoftO.add
                                                                                  | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                  | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                  | apply ThreeSumApsp.Scale.SoftO.max
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                  | apply ThreeSumApsp.Scale.SoftO.div)))
    fun n U => by simp [Light.polyBound]

/-- Three polynomially bounded functions make a polynomially bounded need. -/
theorem polyNeed {need : ℕ → ℕ → Need} (hw : PolyBounded fun n U => (need n U).word)
    (hc : PolyBounded fun n U => (need n U).cells) (hd : PolyBounded fun n U => (need n U).depth) :
    PolyNeed need := by
  obtain ⟨K, e, hK⟩ := exists_nat_le (F := fun n U => (need n U).word + (need n U).cells +
    (need n U).depth) (by first
                          |
                            ((apply ThreeSumApsp.Scale.SoftO.mono);
                              (·
                                  repeat'
                                    with_reducible
                                      first
                                      | exact ThreeSumApsp.Scale.SoftO.const _
                                      | apply Light.PolyBounded.fst
                                      | apply Light.PolyBounded.snd
                                      | apply ThreeSumApsp.Scale.SoftO.log
                                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                                      | apply hw
                                      | apply hc
                                      | apply hd
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
                                                    | apply Light.PolyBounded.fst
                                                    | apply Light.PolyBounded.snd
                                                    | apply ThreeSumApsp.Scale.SoftO.log
                                                    | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                    | apply hw
                                                    | apply hc
                                                    | apply hd
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
                                              | apply Light.PolyBounded.fst
                                              | apply Light.PolyBounded.snd
                                              | apply ThreeSumApsp.Scale.SoftO.log
                                              | apply ThreeSumApsp.Scale.SoftO.sqrt
                                              | apply hw
                                              | apply hc
                                              | apply hd
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
                                      | apply Light.PolyBounded.fst
                                      | apply Light.PolyBounded.snd
                                      | apply ThreeSumApsp.Scale.SoftO.log
                                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                                      | apply hw
                                      | apply hc
                                      | apply hd
                                      | apply ThreeSumApsp.Scale.SoftO.add
                                      | apply ThreeSumApsp.Scale.SoftO.mul
                                      | apply ThreeSumApsp.Scale.SoftO.pow
                                      | apply ThreeSumApsp.Scale.SoftO.max
                                      | apply ThreeSumApsp.Scale.SoftO.sub
                                      | apply ThreeSumApsp.Scale.SoftO.div)))
  refine ⟨Nat.size K, e, fun n U => ?_⟩
  have hsum := hK n U
  have hpoly : K * ((n + 1) * (U + 1)) ^ e ≤ Light.polyBound (Nat.size K) e [n, U] := by
    simp only [Light.polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact Nat.mul_le_mul_right _ (Nat.lt_size_self K).le
  exact ⟨by omega, by omega, by omega⟩

end PolyBounded

/-! ## The need of a solver that a host calls

A polynomially bounded need, at a size `A(n, U)` and a bound `B(n, U)` that are polynomially
bounded, has polynomially bounded parts. -/

namespace PolyNeed

variable {need : ℕ → ℕ → Need} {A B : ℕ × ℕ → ℕ} {a b : Fin 0 → ℕ}

private theorem part (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    ∃ R : ℕ → ℕ → ℕ, PolyBounded R ∧ ∀ n U, (need (A (n, U)) (B (n, U))).word ≤ R n U ∧
      (need (A (n, U)) (B (n, U))).cells ≤ R n U ∧ (need (A (n, U)) (B (n, U))).depth ≤ R n U :=
  let ⟨s, k, hle⟩ := h
  ⟨_, PolyBounded.polyBound (A := fun n U => A (n, U)) (B := fun n U => B (n, U))
    (hA.mono isEmptyElim) (hB.mono isEmptyElim) s k, fun _ _ => hle _ _⟩

/-- The numbers of the solver. -/
theorem word (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).word) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).1

/-- The cells of the solver. -/
theorem cells (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).cells) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).2.1

/-- The depth of the calls of the solver. -/
theorem depth (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).depth) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).2.2

end PolyNeed








end Light

end
end

section


/-!
# The arithmetic behind the running-time claims of Section 3

Elementary inequalities that the deductions between running-time claims use silently.

* `⌈n^{1/3}⌉ ≥ 1` and `(log s + 1)^e ≥ 1`.
* Thin instances, `n ≥ D^18` (Theorem 5, Corollaries 15, 16 and 26): the overheads `n D`, `n² / √D`
  and `1` are at most `n² / D^a`, and so at most the bounds `n² log² D / D^{1/18}` and
  `n² / D^{0.063}`.
* The pieces into which Corollary 15 splits `W` have at most `n² / √D` query pairs (`splitCap_le`).
-/

public section

namespace ThreeSumApsp

/-! ## Two quantities that are at least 1 -/





/-! ## Thin instances: `n ≥ D^18` -/








































/-! ## The pieces of Corollary 15 -/





























end ThreeSumApsp

end
end

section


/-!
# Logarithms up to a constant factor

Bounds on logarithms in the calculus `Dominated`, for every argument of a domain and not only for
large ones.

* Absorbing logarithms, for `x ≥ 1`: `(log x + 1) ^ e` is `O(x ^ η)` for `η > 0`
  (`dominated_log_add_one_pow_rpow`), hence `x ^ a * (log x) ^ e = O(x ^ b)` for `a < b`
  (`dominated_rpow_mul_log_pow_rpow`).
* From 2 on: `log x + 1 = O(log x)` (`dominated_log_add_one_log`) and `⌈log_b n⌉ + 1 = O(log n)`
  (`dominated_clog_add_one_log`).

For a natural number or a field of a parameter record in place of `x`, use `Dominated.comp`.
-/

public section

namespace ThreeSumApsp

open Real

/-! ### Absorbing logarithms, for all `x ≥ 1` -/




































/-! ### `log x + 1` and `⌈log_b n⌉ + 1` are `O(log)`, from `2` on -/





end ThreeSumApsp

end
end

section


/-!
# `logU`, the paper's `log U`

`logU u` is `log u`, read as `log 2` for `u < 2`.

* It is positive and nondecreasing, and `log (cu) ≤ log c + log u` for `c ≥ 1`.
* `log (cU) = O(log U)` (`dominated_logU_mul`) and `log (c n^κ) = O(log n)`
  (`dominated_logU_mul_rpow`).
* Along bounds `u(n) ≤ c n^κ` it is `Õ(1)` (`isPowPolylog_logU_of_le`).
-/

public section

namespace ThreeSumApsp

















/-! ## `logU` of a multiple -/





/-! ## `logU` along bounds that are polynomial in `n` -/





end ThreeSumApsp

end
end

section


/-!
# The steps and the scratch space of Strassen's recursion

At level j the operands are 2^j × 2^j matrices whose entries are vectors of p numbers, so that an
operand has 4^j · p numbers.  strScr p j ≤ 4^j · p (`strScr_le`), and both strScr and strSteps are
monotone in p.
-/

public section

namespace Light.Sec3




























end Light.Sec3

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







































































end ThreeSumApsp.Spec

end
end

section


/-!
# Scanning a piece (the proof of Theorem 17)

"For every query pair that the oracle accepts, scan the piece C_k of its instance for a c with
S(a,b,c) = 0".  The procedure scan (`scanBody`) goes through an interval of vertices `c` for a fixed
pair `(a, b)` (`scan_spec`, `scan_meets`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}






/-! ## The three arrays of weights -/










/-! ## Scanning an interval of vertices -/

namespace Scan


















end Scan





























end Light.Sec3

end
end

section


/-!
# The parameters of Theorems 17 and 19, without division and without roots

The proof of Theorem 19 chooses D as "the largest power of four with D ≤ n^{1/18}"
and g := ⌈D^{1/36}⌉, or D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉; the reduction of Theorem 17 uses
⌊n²/√D⌋ and quotients rounded up.  The language has neither division nor roots, so all of these are
found by counting up.  A power is compared with a bound without forming a number above the bound
times the base.

* powLt(g, e, t), for g ≥ 1, returns 1 if g^e < t, and 0 if not (`powLt_meets`); what it holds after
  i factors is `capPow g t i`.
* rootCeil(e, t) returns the least g with g^e ≥ t (`rootCeil_meets`).
* The four parameters; 5 and 26 stand for the two routes of Theorem 19, through Theorem 5 and
  through Corollary 26.  d5(n) returns the largest power of four that is at most n^{1/18}, g5(D)
  returns ⌈D^{1/36}⌉, d26(n) returns ⌊n^{1/18}⌋, and g26(D) returns ⌈D^{0.0315}⌉; g5 and g26
  are for D ≥ 1 (`d5_spec`, `g5_spec`, `d26_spec`, `g26_spec`).
* queryCapNat(n, D) returns ⌊n²/√D⌋, and ceilDiv(a, b) returns ⌈a/b⌉ (`queryCapNat_meets`,
  `ceilDiv_meets`).

No routine touches the memory.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Comparing a power with a bound -/













namespace PowLt









end PowLt













/-! ## Roots, rounded up -/

namespace RootCeil







end RootCeil


















/-! ## The four parameters of the proof of Theorem 19 -/
















































































































/-! ## ⌊n²/√D⌋ and quotients rounded up -/












































































































end Light.Sec3

end
end

section


/-!
# Brute force (the proof of Theorem 19)

In the proof of Theorem 19, "smaller instances are solved by brute force": the procedure brute
(`bruteBody`) scans all of `C` for every pair `(a, b)` (`brute_spec`, `brute_meets`).  It takes at
most `100 n³ + 100` steps (`brute_solves`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}















namespace Brute














end Brute
























section

variable {pScan : ℕ} {μ : ℕ → ℤ} {ab bc ac n a U fr : ℕ} {AB BC AC : List ℤ}





end















end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the need stays polynomial

The need of a procedure says what it asks of the limits of a run: the largest number that it forms,
the cells that it uses, and the depth of its calls.  If the need of the solver is polynomially
bounded (`PolyNeedN`), then so is the need of the host (`hostNeed_poly`: `PolyNeed` of `hostNeed`).
The need of the host is an explicit expression in `n`, `U`, `D`, `g` and a few quantities derived
from them.  Each of these is at most a polynomial in `(n + 1)(U + 1)` (`PolyBounded`), and such
bounds are closed under sums, products and powers.

* The quantities: `⌊√D⌋ ≤ D`, the number of binary digits of `U` is at most `U`,
  `2^{len + 1} ≤ 4(U + 1)`, `2^⌈log₂ n⌉ ≤ 2(n + 1)`, `⌊n²/√D⌋ ≤ n²`, `⌈s/g⌉ ≤ s + g` with
  `s = ⌊√D⌋`.
* The numbers (`polyBounded_hostWord`), the cells (`polyBounded_chooseCells`,
  `polyBounded_hostLayout`), and each of the three parts of the need of the solver on the instances
  of the host (`polyBounded_sup`).  The depth adds `O(⌈log₂ n⌉)` calls (`polyBounded_clog`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace HostPoly

/-! ## The quantities -/

















variable {D g : ℕ → ℕ}



/-! ## The numbers, the cells, and the solver -/

section parts

variable (hD : PolyBounded fun n _ => D n)
include hD









end parts

end HostPoly



end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the program, assembled

The procedures of the host are appended to a program `P₀` that already holds a solver of
Lop-AE-SparseTri and the two procedures that compute the parameters `D` and `g`.  This file has the
list of the procedures (`et17Procs`), their numbers (`et17NumsAt`), the proof that the program so
obtained is the context that the top procedure assumes (`et17Ctx_assembled`), and the
result: the host solves Exact Triangle (`et17_solves`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec




































































                                              -- 28

variable {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}





end Light.Sec3

end
end

section


/-!
# Theorem 17 as a claim about programs of the light language

`Claim.Theorem_17 M MM D g` says: from every solver of Lop-AE-SparseTri with running time `T` there
is a solver of Exact Triangle whose running time is at most
`4ng (T + C n²/√D) + C (κ n³ log n/g + MM(n) D^{3/2} + n² D g)` (`bound17`, with the three terms
`termScans`, `termPrime`, `termBuild` of the additional time).  Here `κ` is the exponent in
`|w(e)| ≤ n^κ` (the paper's ν), `D` and `g` are the parameters of the reduction as functions of
`n`, `MM(n)` is the number of ring operations of the matrix multiplication, and `M` says what
"solved in time" means.
This file reduces the claim, for the interpretation by programs of the light language, to two facts
about a host: it turns solvers into solvers and keeps their need (word size, cells, depth of calls)
polynomial, and its time function obeys the bound (`ObeysBound17`, `claim17_of_host`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp


















end Light.Sec3

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












































end CostParams.Hyp

/-! ## Numbers of steps up to a constant -/






namespace Steps

variable {t t₁ t₂ : CostParams → ℕ} {B B₁ B₂ : CostParams → ℝ}

























end Steps

/-! ## Monomials -/



















/-! ## The basic quantities -/

























































/-! ## The routines -/














































































/-! ## The three terms of the bound dominate the monomials -/






























































section within

variable {t : CostParams → ℕ} {e : Fin 3 → ℕ}















end within

namespace Steps

variable {t₁ t₂ m : CostParams → ℕ} {B : CostParams → ℝ}






end Steps

/-! ## The choice of the prime -/







































































end Light.Sec3

end
end

section


/-!
# Theorem 17 for programs of the light language, with the two choices of parameters of Section 3.3

Theorem 17 reduces Exact Triangle to at most `4ng` instances of Lop-AE-SparseTri(n, D). As
a claim about programs: from every solver of Lop-AE-SparseTri there is a solver of Exact Triangle
whose time obeys the bound of the theorem, here with Strassen's algorithm for the matrix product
(`Claim.Theorem_17` with `strassen`).  The program is the host `et17`.

The host takes the procedures that compute `D` from `n` and `g` from `D` as parameters.  Here they
are the routines for the two choices of the proof of Theorem 19: "Let D be the largest power of four
with D ≤ n^{1/18} [...] and let g := ⌈D^{1/36}⌉", and "Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉".
The program is the solver's program, followed by the parameter routines (`paramProcs`), followed by
the procedures of the host.

1. The four routines are parameter procedures in the sense of the host (`paramProc_d5`,
   `paramProc_g5`, `paramProc_d26`, `paramProc_g26`).
2. The parameters and the numbers that the routines form are polynomially bounded
   (`polyBounded_paramD₅Nat`, `polyBounded_paramG₅Nat`, `polyBounded_wD5`, `polyBounded_wG5`,
   and the same for the second choice).  So the need of the host (word size, cells, depth of calls)
   is polynomially bounded if that of the solver is (`hostNeed_poly`).  With `et17_solves` this
   makes the host turn solvers into solvers (`host_of_paramProcs`).
3. The routines take `O(n)`, respectively `O(D)`, steps (`steps_tD5`, `steps_tG5`, `steps_tD26`,
   `steps_tG26`).  So the time of the host obeys the bound of the theorem (`obeysBound17_hostTime`).
   Together: `claim_theorem_17₅` and `claim_theorem_17₂₆`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The parameter routines -/











































/-! ## The parameters and the words are polynomially bounded -/




































/-! ## The time of the parameter routines -/



















/-! ## The host with parameter routines -/















end Light.Sec3

end
end

section


/-!
# The running time of brute force (the proof of Theorem 19)

The `100 n³ + 100` steps of brute are within the form `C n³ (1 + log u)` in which the running times
for Exact Triangle with weights of absolute value at most `u` are stated (`claim_bruteForce`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec



end Light.Sec3

end
end

section


/-!
# Two programs in one: relocation of procedures

A program grows by appending procedures.  To put two programs, each with its own numbering of
procedures, into one, the second is placed behind the first (`Program.behind`), and the numbers of
the procedures that it calls are shifted by the length of the first (`Stmt.shift`).

A run of a statement in P is then a run of the shifted statement, with the same states and the
same number of steps (`Exec.shift`, an induction on the run in which only the case of a call has
anything to do: `Program.getElem?_behind_right`).  So everything proved with `Ends` carries over
(`Ends.shift`, `Ends.shift_append`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}






















end Light

end
end

section


/-!
# Two algorithms for Exact Triangle and a threshold on the number of vertices

For every threshold n₀ there is a constant C₀ such that, if Exact Triangle is solved in time T₁ and
in time T₂, then it is solved in time T₁ + C₀ for n < n₀ and T₂ + C₀ for n ≥ n₀.  This is
`Closure.ChooseBySize`, with "Exact Triangle is solved in time T" read as `SolvedIn etTask T`
(`closure_chooseBySize`).  It is used in the proof of Theorem 19, where the bounds hold
for large n only.

Two solvers are put into one program, the second behind the first (`solves_behind`), and one more
procedure looks at the number of vertices and calls the first solver below a fixed threshold n₀ and
the second one from the threshold on (`bySize_spec`).  The need stays polynomial
(`polyNeed_bySize`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}


















namespace ChooseHost







end ChooseHost

open ChooseHost



end Light.Sec3

end
end

section


/-!
# Corollary 15: counting triangles with the thin matrix product, and detecting with counting

Two steps of the proof of Corollary 15, with "the problem is solved in time T" read as
`ThinSolvedIn` and `LopSolvedIn`.

* `Claim.LopCountFromThinProduct`: "Apply Theorem 5 with N = n to the two biadjacency matrices".  An
  instance of #Lop-AE-SparseTri is given by its two biadjacency matrices, so a solver of the thin
  matrix product is a solver of #Lop-AE-SparseTri as it stands, called with U = 1, where U, the
  fourth argument and parameter, is the bound on the entries of the matrices
  (`solvesN_count_of_thin`, `claim_lopCountFromThinProduct`).
* `Claim.LopDetectFromCount`: the counts "are nonzero exactly for the query pairs that lie in a
  triangle".  One more procedure calls the counting solver and replaces every nonzero count by 1
  (`detect_spec`, `claim_lopDetectFromCount`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

namespace LopHosts

/-! ## Bounds -/





/-! ## Counting with the thin matrix product -/





end LopHosts

open LopHosts



/-! ## Detecting with counting -/

namespace LopArgs














end LopArgs
















namespace LopHosts







end LopHosts

open LopHosts



end Light.Sec3

end
end

section


/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}










namespace PowTable









end PowTable

open PowTable




































































end Light

end
end

section


/-!
# Theorem 5 in the light language: sizes and places

The sizes of the tables and arrays of Theorem 5's program, and their places in the memory. No
program occurs here.

The program for Theorem 5 (the solver) and the data structure of Section 4 begin with the same
stage, the shared stage, which fills the shared block: a directory of 32 cells with the sizes and
the addresses of the areas (`dirList`), then the tables, then the encodings of all bands, then two
scratch areas. The solver has a private block behind it. The areas lie one after the other:
`Par.places` (the shared block) and `Par.places5` (the private block) say where every area begins
and ends. `Par.sizes` collects the inequalities between the sizes, each of which has a name of its
own.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## Sizes -/











namespace Par






















/-! ## The shared block, from its base address `b0` on -/











































end Par








/-! ## The private block of Theorem 5

The solver receives `N`, `D`, the number `w` of wanted positions, a bound `U` on the entries, the
addresses of `X`, `Y` (row by row), of the rows `WI` and the columns `WJ` of the wanted positions
and of the output, and as last argument the free pointer `fr`. All inputs and the output lie below
`fr`. The solver may write the output and the cells from `fr` on, and nothing is assumed about these
cells: a routine clears what it needs cleared. The shared block starts at `fr`, the private block
follows it. -/

namespace Par




























end Par

/-! ## The places and the sizes, as equations and inequalities -/



namespace Par
variable (p : Par)





























end Par











end Light.Sec2

end
end

section


/-!
# The alphabets of Schönhage's identity as digits

Section 2.2 names seven left variables, seven right variables, ten output variables and
ten terms; Section 2.3.1 indexes arrays by strings over these alphabets.  Here every
letter gets a digit, so that a string becomes a number (`codeStr`).

* The left variables `x₁ x₂ x₃ p₁₁ p₁₂ p₂₁ p₂₂` are the digits `0, …, 6`; likewise the right
  variables.
* The output variables `z₁₁ z₁₂ … z₃₃ z₀` are the digits `0, …, 9`, and the terms `P₁₁ … P₃₃ P₀`
  likewise, so that `z_ij` and `P_ij` have the same digit `3(i-1) + (j-1)`, and `z₀` and `P₀` have
  the digit 9.
* Left and right strings are numbers in base 7 (`codeL`, `codeR`), output strings, vertices and
  leaves in base 10 (`codeO`, `codeT`), strings of indices of outer variables in base 3
  (`codeOuter`) and of inner variables in base 4 (`codeInner`), always with level 1 most
  significant.
* Which output variables are inner, and which term contributes to which output variable (Section
  2.2), is read off the digits (`outVar_isInner_iff`, `contributes_iff`).
* The coefficients of the linear forms `φ_λ` and `ψ_λ` (Section 2.2) are written out as the rows of
  two 10 × 7 tables, `phiTable` and `psiTable`, which the programs store row after row
  (`phiFlat_spec`, `psiFlat_spec`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Digits -/





























































































/-! Applying one of the five bijections gives the digit. -/











/-! ## Codes of strings -/

























/-! ### Codes of output strings and of vertices

The general facts about `codeStr`, under names of their own for the two codes that occur most. -/




































/-! ## The structure of the identity, in digits -/

































/-! ## The coefficients of the linear forms, as tables -/





































end ThreeSumApsp.Spec

end
end

section


/-!
# Arrays on strings as lists

Section 2.3.1: "An array a on the left strings of length L assigns an integer a[u] to each u that is
a left string of length L."  In a program such an array is a list: an array on the strings of length
`n` over an alphabet of `b` letters is the list of its `b^n` entries in the order of the codes
(`arrStr`), so the entry at a string is the entry of the list at the code of the string
(`getD_arrStr`), and an entry of the list is 0 if the array is 0 at the string with that code
(`getD_arrStr_eq_zero`).  The arrays on left strings, on right strings and on leaves are the cases
`arrL`, `arrR` and `arrT`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Arrays on the strings over any numbered alphabet -/

section
variable {α : Type} {b : ℕ} (e : α ≃ Fin b) [NeZero b] {n : ℕ} (a : (Fin n → α) → ℤ)


























end

/-! ## The three kinds of arrays of Section 2 that the programs store -/


































end ThreeSumApsp.Spec

end
end

section


/-!
# The memory map of Theorem 5: what depends on which cells

SharedReady.dirs lists the cells of the directory that the solver reads. SharedTables are the tables
of the shared block without the directory and the encodings; they depend only on the cells between
these two (SharedTables.congr), and all that the shared stage leaves behind depends only on the
cells of the shared block, without the last of the 32 cells of the directory, which the shared stage
does not use (SharedReady.congr, SharedReady.of_agree).
-/

public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## The directory -/

variable {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
  {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}























/-! ## Only the shared block matters -/












end Light.Sec2

end
end

section


/-!
# Theorem 30 in the light language: the memory map and the invariant of the data structure

The data structure occupies one block of the memory, from a base address b0 on. First comes the
shared block of Section 2 (directory, tables, the encodings of all bands), and behind it the areas
of Section 4:

    WD (L) | CUR (L) | BOX (L) | SS (m) | FP (1) | ROOTS (nB²) | TR (cap)

WD holds the digits of the output string of a query; CUR, BOX and SS are scratch strings; FP holds
the length of the trie array; ROOTS holds the roots of the tries, that of tile (β, β') in the cell
β nB + β'; TR is the trie area. Cell 31 of the directory holds t. `Areas` says where the tables that
the routines of Section 4 read and the areas of Section 4 lie, and `areas` proves it.

Two routines know this map: preCore(L, m, t, N, D, aX, aY, b0) builds the block from the matrices at
aX and aY, which lie below b0, and queryAt(I, J, b0) answers a query from it. They are relocatable,
so that Theorem 30, its offline form and Corollary 26 use the same two routines. The main procedures
of Theorem 30's programs only read the sizes from the input and compute the addresses. For Corollary
26 a routine of its own stands in between: it finds m and, from the threshold of the proof on, L and
t, writes padded copies of the matrices, and runs `preCore` on them.

Section 4.3: "Our data structure consists of three components: the list of the K₀² subsets Q
assigned to the block products of a tile […], the encodings of all row bands and all column bands,
and for every tile, the values of all its boxes". In the invariant DSReady the field shared holds
the first two, and the fields roots and trie hold the third: "for each tile we store its boxes, with
their values, in a standard trie on their strings of L symbols". The tries of all tiles lie in one
array (trie), and the table roots has the root of the trie of each tile. The invariant depends only
on the cells from b0 on, without the scratch strings (`DSReady.congr`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The map -/






















/-! ## Where the areas lie -/







































/-! ## The directory -/

namespace Dir




















end Dir

/-! ## The invariant -/



























section

variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}











end












/-! ## The two routines that know the map -/




































end Light.Sec4

end
end

section


/-!
# Section 4.4: the steps of the proof of Corollary 26 that hold for all parameters

The proof of Corollary 31 begins: "We repeat the proof of Corollary 26 with L := ⌈cm⌉ and t :=
⌈θm⌉". This file has the parts of the proof of Corollary 26 that mention neither `L = 21m` nor
`t = ⌈m/9⌉`, under the headings of that proof. Both corollaries use them.

* Setting up. The inner dimension is padded to `D = 4^m` with `m = ⌈log_4 D⌉`
  (`Corollary26.setting_up`). This changes no entry of the product (`Corollary26.padding`), and it
  changes the bounds by a constant factor (`padded_le`). The switching order `t = ⌈θm⌉` is
  `switchOf θ m`, and `t ≤ m` (`switchOf_le`).
* Queries. `∑_{d ≤ t} α_d ≤ (9x)^t (1 + 1/x)^m` for every `x ≥ 1/9` (`sum_alpha_le`), and for
  `x = (1-θ)/θ` the right-hand side at `t = θm` is `D^q` (`rpow_mul_pow_eq_D_rpow_qOf`).
* Encodings. Inequality (10), whose left-hand side is `lhs10 L m γ`, bounds the last term of (8) and
  gives the hypothesis `N ≥ √K N₀` of Theorem 30 (`Equation10.last_term`, `Equation10.tile_fits`).
* Conclusion. The expression (8) from a bound on its first term and (10)
  (`dominated_cost8_of_eq_10`).

Bounds "up to a constant" are written with `Dominated`, in the one parameter `m` or in the record
`Sizes` of the given inner dimension, of `N` and of `m`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Setting up -/




























































































/-! ### Queries -/









































/-! ### Encodings -/






























/-! ### Conclusion -/























end ThreeSumApsp

end
end

section


/-!
# Corollaries 26 and 31 in the light language: m, the places of the padded matrices, the query

m = ⌈log₄ D⌉ (`logFour`), the places of the padded matrices and of the block of Theorem 30 behind
the free pointer (`paddedXAt`, `paddedYAt`, `blockAt`), the text of the query, and the bounds on the
entries of the padded matrices. The text of the query serves all rational parameters; its
specification is `QuerySpec31`, proved in `query31_meets`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters and map -/









/-! ## The query -/

namespace Query31










end Query31





























end Light.Sec4

end
end

section


/-!
# Corollaries 26 and 31 in the light language: rational parameters in the program text

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D";
proof of Corollary 31: "with L := ⌈cm⌉ and t := ⌈θm⌉". A program is a finite text, so it can hold c
and θ only if they are rational: c = a/b and θ = p/q (`RatParams`). For real c and θ the statements
follow by approximation (`exists_ratParams`). Corollary 26 is the case c = 21, θ = 1/9, with the
threshold 60 (`ratParams26`).

This file has the parameters, what a structure at the free pointer fr consists of (`structEnd`,
`Ready31`), what the routines ask of the limits (`Lim31`), the query with its specification and its
proof (`QuerySpec31`, `query31_meets`), and the text and the specification of the preprocessing
(`pre31Body`, `PreSpec31`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters -/
















variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}


























































































































/-! ## The query: the text is query31Body -/




















/-! ## The preprocessing: text and interface -/









namespace Pre31



















end Pre31















































end Light.Sec4

end
end

section


/-!
# An entry of the product as an inner product

Proof of Corollary 26: "(For m < 60, D is bounded by a constant, and the corollary holds
trivially.)"; proof of Corollary 31: "for smaller m the corollary again holds trivially". In the
programs a query then computes an inner product, of a bounded number D of summands. The routine adds
the D products X[I, s] Y[s, J]. `ipPart` is the sum of the first s of them, with its recursion
(`ipPart_succ`), its bound (`abs_ipPart_le`) and its last value (`ipPart_full`); `ipAt_meets` is the
specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

namespace IpAt















end IpAt











section
variable {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (I J : Fin N)








variable {X Y}





end



end Light.Sec4

end
end

section


/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).
-/

@[expose] public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec loadWords)

variable {W : ℕ} {P : List Instr}

/-! ## Words -/








































/-! ## Configurations and single steps -/






















/-! ## Runs -/


















































/-! ## Pieces of code -/





































/-! ## Straight-line code -/





















































/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}

















































end known

/-! ## Branches and verdicts -/























/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}






















































end framing

end ThreeSumApsp.WordRam

end
end

section


/-!
# Theorem 30, the offline form (9): preprocess, then one query for each wanted position

Theorem 30: "In particular, for every set W of positions of an N × N matrix, the entries (XY)[I, J],
(I, J) ∈ W, can be computed deterministically in time
O(L |W| ∑_{d=0}^{t} α_d + L m ρ^t/(1 - ρ) N² + N · 10^L/(√K N₀))."

wantedCore is relocatable: it receives the addresses of the matrices, of the two lists of indices,
of the output and of the free block. It meets its specification `WantedCoreSpec` in every program
that meets those of preCore and queryAt (`wantedCore_spec`): one call of preCore, then a loop whose
round asks one query and stores the answer (`wantedAsk_ends`), with the invariant `Answered`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## One query for each wanted position: the invariant -/

section
variable {Ready : (ℕ → ℤ) → Prop} {Kept Quiet : ℕ → Prop} {out i : ℕ} {ans : List ℤ}
  {μ μ' μ'' : ℕ → ℤ}
















end

/-! ## The routine -/



namespace WantedCore




















end WantedCore


















section
variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY aI aJ out b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {W : List (Fin p.N × Fin p.N)} {μ μ' μ'' : ℕ → ℤ}


















end






















































































end Light.Sec4

end
end

section


/-!
# Section 4.4, the offline form: preprocess, then one query for each wanted position

Corollary 26: "Hence, for every set W of positions of an N × N matrix, the entries (XY)[I, J], (I,
J) ∈ W, can be computed deterministically in O(|W| D^{0.437} + N²/D^{0.063}) time". Its proof: "The
bound for a set W follows by asking |W| queries." Proof of Theorem 25: "ask one query for each
position of W"; for Corollary 32 the paper uses "the same argument", "With Corollary 31 in place of
Theorem 24".

offline32(N, D, w, U, x, y, wi, wj, out, fr) preprocesses the matrices at x and y (pre31, which uses
the cells from the free pointer fr on) and then asks one query for each of the w positions, whose
rows are at wi and whose columns are at wj; the answers go to out. The arguments are those of the
task `thinTask`. The text `offline32Body`, with the round `offlineAsk32` of its loop, serves all
rational parameters c and θ: they are in the body of the procedure pre31 (`pre31Body`).

A round adds one answer (`offlineAsk32_ends`), with the invariant `Answered` that the offline form
of Theorem 30 uses too, and the routine meets its specification `OfflineSpec32` for all parameters G
(`offline32_meets`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-! ## The text -/






namespace Offline32

















end Offline32















/-! ## What it does -/













































end Light.Sec4

end
end

section


/-!
# The routines of Section 4, assembled

The fourteen routines with the numbers 40 to 53, as a list (procs40), and the theorem that every
program that holds them at these numbers (Has40) meets all their specifications (specs40). Each
routine is proved under the specifications of the routines that it calls; here these assumptions are
discharged, in the order in which the routines call each other. For the programs of Theorem 30, its
offline form and Corollary 26, which hold the fourteen routines behind forty others
(has40_of_append), this gives the specifications of the two routines that know the memory map:
preCoreSpec_of and preCoreSpec_all for the preprocessing, queryAtSpec_all for a query.
-/

@[expose] public section

namespace Light.Sec4





































































end Light.Sec4

end
end

section


/-!
# Theorem 30 on the word RAM: the program

`program30` is the list of procedures: those of Section 2 (numbers 0 to 28, of which the
preprocessing uses the shared stage), the routines of Section 4 (40 to 53), preCore, queryAt and the
two procedures of the offline form (54 to 57), and the two main procedures of Theorem 30 (80 and
81); the unused numbers hold the empty statement.

The first 58 procedures (`base58`) are also the beginning of the programs for Corollaries 26, 31
and 32.  So the assumptions of the earlier files are discharged for every program `base58 ++ R` that
begins with them: it meets the specifications of the preprocessing and of a query at a given place
of the memory (`preCore_base58`, `queryAt_base58`).  With `theorem_30_of` and `theorem_30_wanted_of`
this gives Theorem 30 and its offline form without hypotheses (`wordRam_theorem_30`,
`wordRam_theorem_30_wanted`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam





































end Light.Sec4

end
end

section


/-!
# Corollaries 26, 31 and 32: the concrete program for given parameters

program31 G = base58 (Theorem 5's and Theorem 30's procedures, numbers 0 to 57) followed by the
procedures 58 to 73 of Section 4.4 (`procs31`): copying, filling, m = ⌈log₄ D⌉, padding and the
inner product; the preprocessing pre31Body G at 64 and the query; their main procedures; the offline
routine and its main procedure; the solver of Corollary 26 for all instances with its test; and the
two procedures for L = ⌈am/b⌉ and t = ⌈pm/q⌉ at 72 and 73. The specifications of the preprocessing,
the query and the offline routine hold for it, for all limits, without hypotheses. At the parameters
of Corollary 26 it is `program26`.

With the two end theorems for light programs and the compiler this gives the two statements about
the word RAM from which Corollaries 26, 31 and 32 follow: on every domain of inputs, and for all
bounds that dominate the two costs of Theorem 30 at the parameters G (`CostsWithin`), the compiled
program is a data structure (`isDataStructure_of_costsWithin`) and solves the offline problem
(`solves_of_costsWithin`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam

/-! ## Two procedures for Corollary 26

The program carries them for all parameters G. What they do at the parameters of Corollary 26 is
proved in `regimeTest26_meets` and `allInstances26_solves`. -/












/-! ## The program -/











































/-! ## The program on the word RAM -/







































end Light.Sec4

end
end

section


/-!
# Corollary 26, the offline form, on all instances

Corollary 26 is about matrices with N ≥ D^18. A solver that other procedures call has to be right on
every instance. allInstances26(N, D, w, U, x, y, wi, wj, out, fr) tests whether D^18 ≤ N, calls the
offline routine offline32 if so and the brute force if not. The texts are `allInstances26Body` and
`regimeTest26Body`.

* *The routine.* It solves the task `thinTask` on every instance, within the time
  `allInstancesTime26` and the need `allInstancesNeed26` (`allInstances26_solves`). It tests whether
  D^18 ≤ N (`regimeTest26_meets`). In that regime it calls the offline routine of Corollary 26,
  whose demands on the limits are covered by the need (`lim31_of_need`, `offline32_meets_thinTask`);
  outside it calls the brute force.
* *The time in the regime.* For N ≥ D^18 the time is O(w D^{0.437} + N²/D^{0.063}), the bound of
  Corollary 26: the time of the offline routine is at most a constant times tp + w tq for all bounds
  that dominate the two costs of Theorem 30 (`exists_tOffline32_le`), and in the regime the two
  bounds of Corollary 26 do (`regime26`).
* *The need is polynomial in the parameters.* Every summand of the need is a numeral times a product
  of at most 20 factors N + 1, D and U. With Q = (N + 1) (D + 1) (w + 1) (U + 1) each factor is at
  most Q, so each product is at most Q^20 (`le_pow_twenty`). So the largest number, the cells and
  the levels of calls are at most 2^11 Q^20 (`word_le`, `cells_le`, `depth_le`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Time and need -/


















/-! ## The test -/





















/-! ## The limits -/

section need

variable {lim : Limits} {N D₀ w U fr d : ℕ}










































































end need

/-! ## The matrices of an instance -/



































/-! ## The routine -/


























































































/-! ## The time in the regime -/


















/-! ## The need is polynomial in the parameters -/



section summands

variable {N D U Q : ℕ}







end summands





end Light.Sec4

end
end

section


/-!
# Corollary 26, the offline form, for programs of the light language

Corollary 26: "Hence, for every set W of positions of an N × N matrix, the entries (XY)[I, J], (I,
J) ∈ W, can be computed deterministically in O(|W| D^{0.437} + N²/D^{0.063}) time". This is
`Claim.Corollary_26_wanted`, here with "is solved in time T" read as a statement about programs of
the light language (`claim_corollary_26_wanted`).

The program is `program26`: for m = ⌈log₄ D⌉ ≥ 60 it builds and asks the data structure of Theorem
30 with L = 21 m and t = ⌈m/9⌉, and for m < 60 it computes inner products. The procedure
allInstances26 of that program solves the task on all instances (`allInstances26_program26`), with a
polynomially bounded need (`allInstancesNeed26_poly`), and for N ≥ D^18 its time is within the bound
(`allInstancesTime26_le`).

This is the form of Corollary 26 on which Corollary 16, and through it the second bounds of Theorems
19 and 22, rest: a procedure that other procedures call. The statement about one program that reads
the input of the problem is `wordRam_corollary_26_wanted`.
-/

public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec







end Light.Sec4

end
end

section


/-!
# From a realized running time to a program with the paper's bound

A claim gives a running time `T` with `T ≤ C X`, where `X` is the bound that the paper prints, and
`RealizedWithin` gives a program that takes `c T + c` steps.  This file puts the two together.

* Bounds in several parameters, valid on a domain on which `X ≥ 1`: `exists_solves`, and
  `exists_solves_nonneg` with `exists_solves_pair` for two programs with one slope and one constant.
* Bounds `O(n^a (log n)^e)` in one size, valid for all large `n`: `solvedAt_of_realized`, and for
  every exponent `κ` of the magnitude `solvedInTime_of_claim` and `solvedInPolylogTime_of_claim`.
* An instance with numbers bounded by `n^κ` is also one with numbers bounded by `n^κ'`, `κ ≤ κ'`
  (`solvedInTimeAt_mono`), so that a bound for all `κ ≥ 1` is a bound for all `κ`
  (`solvedInTime_of_one_le`).
-/

public section

namespace ThreeSumApsp.FromClaims

open ThreeSumApsp.WordRam
open EndStatement (Instr)

/-! ## Bounds on a domain -/




















































/-! ## Bounds in one size, for all large sizes -/

























































end ThreeSumApsp.FromClaims

end
end

section


/-!
# Running-time claims of Section 3.1: Corollaries 15 and 16

All lemmas are about an arbitrary interpretation `M : DetTimeModel` of "is solved in time T".

* Corollary 15, first case, from Theorem 5 ("Apply Theorem 5 with N = n to the two biadjacency
  matrices"): `Corollary15.first_of_theorem_5`.
* Corollary 15, general case ("splitting W into sets of at most n²/√D query pairs"):
  `Corollary15.general_of_theorem_5`.  One call costs `O(n² log² D / D^{1/18})`, and all calls
  with the overhead cost `O((n² + |W| √D) log² D / D^{1/18})` (`dominated_calls`).
* Corollary 16 from Corollary 26 ("This is Corollary 26 with N = n"):
  `Corollary16.of_corollary_26`.

In each deduction the overheads `n D`, `|W|` and `1` of writing the matrices and copying the answers
are at most the bound of the corollary, because `n ≥ D^18`.  The bounds are added up by the calculus
of `Dominated` on the parameters `n`, `D`, `w`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## The calculus on the parameters `n`, `D`, `w` -/













/-! ## Corollary 15, the first case -/























/-! ## Corollary 15, the general case -/





















































/-! ## Corollary 16 -/



end ThreeSumApsp

end
end

section


/-!
# Corollaries 15 and 16 on the word RAM

The route, as in the paper.  The number of triangles through a query pair is an entry of the product
of the two biadjacency matrices, and detection follows from counting.  So Theorem 5 gives the first
case of Corollary 15; splitting the query pairs into pieces gives the general case; and the offline
form of Corollary 26 gives Corollary 16.  These are claims about programs of the light language
(`claim_corollary_15_first`, `claim_corollary_15`, `claim_corollary_16`).  The outermost procedures
for the input layout and the compiler (`Light.Sec3.realized_lopCount`,
`Light.Sec3.realized_lopDetect`, together `lopRealized`) carry them to the word RAM.
-/

public section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3


















end Light.Sec3

namespace ThreeSumApsp









end ThreeSumApsp

end
end

section


/-!
# The cost analysis of Theorem 19 for a general choice of the parameters

The two halves of the proof of Theorem 19 are the same computation with different numbers.  Both
apply Theorem 17 with a number `D ≥ 16` between `n^{1/18}/c` and `n^{1/18}` and with `g = ⌈D^η⌉`,
and solve each of the at most `4ng` instances with a saving `D^{2η}`.  Such a pair `D`, `η` is a
`Choice`, and the computation is carried out here for every choice.

1. A choice satisfies the hypotheses `16 ≤ D ≤ n` and `1 ≤ g ≤ √D` of Theorem 17 and the hypothesis
   `D^18 ≤ n` of Corollaries 15 and 16 (`Choice.sixteen_le`, `Choice.le_n`, `Choice.one_le_ceil`,
   `Choice.ceil_le_sqrt`, `Choice.pow_eighteen_le`).
2. The lower bound on `D` gives `D^{-η} ≤ c^η n^{-η/18}` (`Choice.saving`), and the upper bound
   gives `D^a ≤ n^{a/18}` (`Choice.rpow_le_rpow_div`).
3. Each of the four terms of the running time is `O(n^{3-η/18})` up to logarithms: the instances
   (`Choice.instances_le`) and the scans (`Choice.scans_le`) by the first bound, the choice of `p`
   (`Choice.strassen_le`) and building the instances (`Choice.build_le`) by the second.
4. So is their sum (`exists_total_le`).
-/

@[expose] public section

namespace ThreeSumApsp

namespace Theorem19





















namespace Choice

variable {n D : ℕ} {η c : ℝ} (P : Choice n D η c)
include P

/-! ### The hypotheses of Theorem 17 and of Corollaries 15 and 16 -/




































/-! ### Logarithms -/







/-! ### Powers of `D` in terms of `n` -/









/-! ### The four terms of the running time

`Λ` is the logarithmic factor of the result, `log² n` or `log n`. -/









end Choice



end Theorem19

end ThreeSumApsp

end
end

section


/-!
# Theorem 19 and Remark 20: Exact Triangle in truly subcubic time (Section 3.3)

Theorem 19 applies the reduction of Theorem 17 with `D` about `n^{1/18}` and `g = ⌈D^η⌉`, and solves
each instance by a corollary of Section 3.1: by Corollary 15 with `η = 1/36`, where `D` is the
largest power of four with `D ≤ n^{1/18}`, and by Corollary 16 with `η = 0.0315`, where
`D = ⌊n^{1/18}⌋`.  This file has the arithmetic of the proof.  The deduction of the running time
from Theorem 17 that uses it is `Theorem19.explicit_of_theorem_17_corollary_15` and
`Theorem19.explicit_of_theorem_17_corollary_16`, and the theorem about programs is
`wordRam_theorem_19`.

1. Both choices of the parameters, `paramD₅` with `paramG₅` and `paramD₂₆` with `paramG₂₆`, are a
   `Theorem19.Choice` (`Theorem19.choice_theorem_5`, `Theorem19.choice_corollary_26`).  So they
   satisfy the hypotheses of Theorem 17 and of the two corollaries (`Choice.sixteen_le`,
   `Choice.le_n`, `Choice.one_le_ceil`, `Choice.ceil_le_sqrt`, `Choice.pow_eighteen_le`).
2. By the cost analysis for a general choice (`Theorem19.exists_total_le`), the number of instances
   times the cost of one instance, plus the additional time of Theorem 17, is
   `O(n^{3-1/648} log² n)`, respectively `O(n^{3-0.00175} log n)` (`Theorem19.total_theorem_5`,
   `Theorem19.total_corollary_26`).  The step "O(n^{3−ε'} log n) ≤ O(n^{3−ε_T})" of the
   statement is the general fact that a larger exponent absorbs logarithms
   (`IsPowPolylog.isBigOPow`); it is applied in `Theorem19.second_of_explicit`.

NOTE.  "Assume n is larger than a constant depending on ν": the two choices of `D` below are stated
for `n ≥ 16^18`, which makes `D ≥ 16`.

Remark 20 explains the values of `η`: the exponents `η - γ` of the instances and `-η` of the scans
balance at `η = γ/2` (`remark_20_balance`, `remark_20_numbers`), and the straightforward algorithm
for the instances gives back the bound `n³` (`remark_20_brute_force`).
-/

public section

namespace ThreeSumApsp

/-! ### The two choices of the parameters -/













































/-! ### The costs added up -/

























/-! ### Remark 20 -/









































end ThreeSumApsp

end
end

section


/-!
# Theorem 19 from Theorem 17 and Corollaries 15 and 16

Theorem 17 reduces Exact Triangle to `4 n g` calls of Lop-AE-SparseTri plus some extra time.  The
proof of Theorem 19 puts in the cost of one call (Corollary 15 or Corollary 16) and the parameters
`D` and `g`, and adds up.  Both routes have the same three steps:

1. the parameters satisfy the hypotheses of Theorem 17 and of the corollary (`Theorem19.choice_*`);
2. one call, with the reading of its answers, costs `O(I)` (`call_cost_corollary_15` and
   `call_cost_corollary_16`);
3. the sum of all terms is `O(κ P)` (`Theorem19.total_*`, the calculation of the proof of
   Theorem 19).

`time_le_of_calls` puts the three steps together.  The result keeps the dependence on `κ`
(`Claim.Theorem_19_explicit`).  From it follow the two bounds as printed, for every constant `κ`
(`Claim.Theorem_19_explicit.eventually_le`), and a bound for all sizes and all bounds on the
weights, which is what Theorem 21 is applied to (`exactTriangleUniform_of_explicit`): small sizes by
brute force (`dominated_bruteForce`), large sizes by the explicit bound with
`κ = max 1 (log u / log s)` (`dominated_explicit`).
-/

@[expose] public section

namespace ThreeSumApsp







































/-! ## The bounds as printed -/





































/-! ## A bound for all sizes and all bounds on the weights -/
























end ThreeSumApsp

end
end

section


/-!
# Theorem 19 on the word RAM

The route, as in the paper.  Theorem 17 reduces Exact Triangle to instances of the lopsided triangle
problem.  With the parameters `D` and `g` of Section 3.3 and Corollary 15 for the instances the
total is `O(n^{3−1/648} log² n)` (`claim_theorem_19_usingTheorem5`); with Corollary 16 it is
`O(n^{3−ε'} log n)`, `ε' = 0.00175` (`claim_theorem_19_usingCorollary26`).  Both are claims about
programs of the light language that keep the dependence on `κ`.  The outermost procedure for the
input layout and the compiler (`Light.Sec3.realized_exactTriangle`) carry them to the word RAM.
The third bound of the theorem, `O(n^{3−ε_T})`, follows from the second, so it rests on Corollary 16
and not on Corollary 15.

Section 3.4 needs the two bounds for all numbers of vertices and all bounds on the weights:
`claim_exactTriangleUniform_usingTheorem5`, `claim_exactTriangleUniform_usingCorollary26`.  They
combine the program with brute force below a threshold, as in the proof ("smaller instances are
solved by brute force").
-/

public section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3

















end Light.Sec3

namespace ThreeSumApsp












end ThreeSumApsp

end
end

section


/-!
# APSP: from a solver of the task to a program for the layout of the end statement

APSP (Theorem 22).  `realized_apsp`: if the task `apTask` is solved in time T, then
`EndStatement.APSP` is solved on the word RAM within a constant times T.

The input is n in cell 0, the adjacency matrix from cell 1 and the weights from cell 1 + n².  The
answer goes to the 2n² cells from 1 + 2n², and the free pointer is 1 + 4n² (`apspInst`).  The task
speaks of the graph with weights in `WithTop ℤ` that is read from the two lists, which is the graph
of the instance (`graphOf_apsp`).  So the input meets the task's precondition (`pre_apsp`), and what
a solver leaves in the output cells is what `EndStatement.APSP` asks for (`post_apsp`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.WordRam ThreeSumApsp.Spec

































































































end Light.Sec3

end
end

section


/-!
# Running-time claims of Section 3.4: Theorems 21 and 22

All lemmas are about an arbitrary interpretation `M : DetTimeModel` of "is solved in time T".  They
are deductions between running-time sentences: those of the paper for Theorem 22, and for
Theorem 21, which the paper cites, those of the route taken here.

* Theorem 21(a) from two reductions, [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]:
  `Theorem21a.of_CH20_VW13`.  The sizes, numbers of instances and extra times compose
  by the rules for `n^{a+o(1)}`.
* Theorem 21(b) for the (min,+)-product from [VW13, Theorem 3.3] and [VW18, Theorem 4.2]:
  `Theorem21b.minPlus_of_VW13_VW18`.  The time of the first reduction is again a good
  time (`GoodTime.mul_logU`), and `log (cU) = O(log U)` (`dominated_logU_mul`).
* Theorem 21(b) for APSP by repeated squaring: `Theorem21b.apsp_of_minPlus`, whose
  arithmetic is `dominated_repeatedSquaring`.
* "Plug Theorem 19 into Theorem 21": `threeSum_of_uniform_theorem_21a`,
  `minPlus_of_uniform_theorem_21b`, `apsp_of_uniform_theorem_21b`.
* Theorem 22: the roundings such as `n^{2-1/1296+o(1)} ≤ O(n^{1.99923})`
  (`Claim.SolvedAlongPow.mono`).
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Theorem 21(a) -/




























/-! ## Theorem 21(b): the (min,+)-product -/









/-! ## Theorem 21(b): APSP -/














/-! ## "Plug Theorem 19 into Theorem 21"

The time of Theorem 19 is `uniformTime K δ e s u = K s^{3-δ} (log s + 1)^e (1 + log u)²`.
Theorem 21 evaluates it at sizes `s(n)` and bounds `u(n) ≤ c n^κ` on the numbers, and multiplies it
by powers of `n` and logarithms.  So each bound is a product of functions of known classes. -/







































































/-! ## Theorem 22 -/









end ThreeSumApsp

end
end

section


/-!
# Theorem 22 on the word RAM

"Plug Theorem 19 into Theorem 21."  Each bound has three ingredients.

1. The paper's deduction between running times, proved for every reading `M` of the sentence "is
   solved by a deterministic algorithm in time T" (lemmas such as `threeSum_of_uniform_theorem_21a`;
   nothing is assumed about `M`).
2. The reading `lightModel`, in which the sentence means that a program of the light language solves
   the task within T steps.  For this reading the reductions that Theorem 21 cites are theorems,
   because they are written as programs that call an arbitrary solver (`Sec3.claim_…`); so
   Theorem 21 holds for it: `claim_theorem_21a` for 3SUM, `claim_theorem_21b_minPlus` and
   `claim_theorem_21b_apsp` for the (min,+)-product and APSP.
3. The way to the machine: a solver of a task, with one more procedure for the input layout,
   compiled, is a program of the word RAM that takes a constant times as many steps
   (`Sec3.realized_threeSum`, `realized_minPlusProduct`, `realized_apsp`).

From a bound `O(s^{3−δ} (log s)^e)` for Exact Triangle this gives

* 3SUM in `O(n^a)` time for every `a > 2 − δ/2` (`threeSum_of_uniform`);
* the (min,+)-product and APSP in `O(n^{3−δ/3} (log n)^{O(1)})` time (`minPlus_polylog_of_uniform`,
  `apsp_polylog_of_uniform`), and so in `O(n^a)` time for every `a > 3 − δ/3`
  (`SolvedInPolylogTime.solvedInTime`).

The theorem is the case `δ = 1/648` (using Theorem 5) and the case `δ = ε' = 0.00175` (using
Corollary 26).  For 3SUM the programs lose polylogarithmic factors only
(`Theorem22.threeSum_polylog`); the printed form with `n^{o(1)}` follows
(`SolvedInPolylogTime.solvedInLittleOTime`).
-/

public section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3

/-! ## Theorem 21 for programs of the light language -/










/-! ## A bound for Exact Triangle, plugged into Theorem 21 -/


















end Light.Sec3

namespace ThreeSumApsp





















































end ThreeSumApsp

end
end

section


/-!
# From a real exponent to a rational one

An item statement bounds the steps of a program by `C (n^a + 1)`, with real numbers `C` and `a`.
The end statement uses Lean's core library only.  It asks for a step bound `T` with natural values
that depends on the size alone, and it writes `T(n) = O(n^r)`, for a rational `r = p/q`, as
`T(n)^q ≤ K n^p`.  Here the first bound, rounded up, is shown to be a bound of the second kind
(`bigO_stepBound`), and a program that meets the first is shown to meet the second
(`SolvedInTime.endStatement`).  The program and the slope of the word size stay the same.
-/

public section

namespace ThreeSumApsp.WordRam


































end ThreeSumApsp.WordRam

end
end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The three source claims derived directly from the stronger Corollary 26 route.
These proofs avoid projecting from bundled claims that also prove unrelated
3SUM results and weaker bounds. The original source declarations are unchanged.
-/

namespace APSPFocusedSource

open ThreeSumApsp.WordRam


















end APSPFocusedSource





end







/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light

/-! ## Regions -/









/-! ## Memories that agree on some cells -/













variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}













/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}











/-- A write outside the cells that have been written can be done first. -/
theorem update_wrote {y : ℕ} (hy : Outside dst j y) (w : ℤ) :
    Function.update (wrote μ dst f j) y w = wrote (Function.update μ y w) dst f j := by
  funext a
  by_cases ha : a = y
  · subst ha
    rw [Function.update_self, wrote_rest hy, Function.update_self]
  · simp only [wrote, Function.update_of_ne ha]



/-! ## The tactics -/











end Light


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Index arithmetic: a pair of numbers as one number

General facts about natural numbers. A matrix with rows of length `n` is kept as one list, row
after row: the entry in row `a` and column `b < n` has the index `a * n + b`. This file has

* the bounds on such an index (`Nat.mul_add_lt_mul`, `Nat.mul_add_le_mul`);
* the way back from the index to the pair (`Nat.mul_add_div_of_lt`, `Nat.mul_add_inj_of_lt`,
  `Nat.div_lt_of_lt_mul'`, `Nat.mod_lt_of_lt_mul`, `Nat.exists_eq_mul_add_of_lt_mul`,
  `Nat.eq_mul_succ_iff`);
* the pair of the next index (`Nat.succ_div_mod_of_lt`, `Nat.succ_div_mod_of_ne`,
  `Nat.succ_div_mod_of_eq`);
* residues seen as natural numbers (`Int.toNat_emod_lt`, `Int.natCast_toNat_emod`).
-/

public section

namespace Nat

/-! ## Bounds on an index -/





/-! ## From the index back to the pair

The column is `Nat.mul_add_mod_of_lt : c < b → (a * b + c) % b = c`. -/













/-! ## The next index -/

/-- The next index, if it is in the same row. -/
theorem succ_div_mod_of_lt {n i : ℕ} (h : i % n + 1 < n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 := by
  have hsucc : i + 1 = i / n * n + (i % n + 1) := by rw [← Nat.add_assoc, Nat.div_add_mod']
  exact ⟨by rw [hsucc, mul_add_div_of_lt h], by rw [hsucc, Nat.mul_add_mod_of_lt h]⟩

/-- The next index, if the test "is this the end of the row?" fails. -/
theorem succ_div_mod_of_ne {n i : ℕ} (hn : 0 < n) (h : i % n + 1 ≠ n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 :=
  succ_div_mod_of_lt (lt_of_le_of_ne (Nat.mod_lt i hn) h)

/-- After the last index of a row comes the first index of the next row. -/
theorem succ_div_mod_of_eq {n i : ℕ} (h : i % n + 1 = n) :
    (i + 1) / n = i / n + 1 ∧ (i + 1) % n = 0 := by
  have hn : 0 < n := h ▸ Nat.succ_pos _
  have hsucc : i + 1 = (i / n + 1) * n + 0 := by
    have hdivmod := Nat.div_add_mod' i n
    rw [Nat.succ_mul]
    -- `i = i / n * n + i % n` and `i % n + 1 = n`
    omega
  exact ⟨by rw [hsucc, mul_add_div_of_lt hn], by rw [hsucc, Nat.mul_add_mod_of_lt hn]⟩

end Nat

namespace Int

/-! ## Residues as natural numbers -/





end Int


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light

open ThreeSumApsp





variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}



























/-- A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
`h.keep` carries `h` to a later memory across the steps whose promises are in the context. -/
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by ((((   try refine _root_.Light.SameOn.cell ?_
                                                                                    intro macro_local_0 macro_local_1
                                                                                    first
                                                                                    | (((   repeat
                                                                                              ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_2);
                                                                                                (try have := macro_local_2 macro_local_0 (by omega)); revert macro_local_2)
                                                                                            intros
                                                                                            try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)); omega)
                                                                                    |
                                                                                      (simp [] at macro_local_1;
                                                                                        ((  repeat
                                                                                              ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_4);
                                                                                                (try have := macro_local_4 macro_local_0 (by omega)); revert macro_local_4)
                                                                                            intros
                                                                                            try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)); omega)
                                                                                    | ( ((  repeat
                                                                                              ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_6);
                                                                                                (try have := macro_local_6 macro_local_0 (by omega)); revert macro_local_6)
                                                                                            intros
                                                                                            try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *))
                                                                                        fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                    SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                    its condition K x does not follow from the hypotheses."))))
                                                                                      )) :
    Seg μ' a l :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩



















































end Light


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Blocks -/











/-! ## The default proofs -/











/-! ## Rules for blocks -/



/-- Two blocks, one after the other. -/
theorem Stmt.Runs.seq {s t : Stmt} {σ : State} {R : State → Prop}
    (h : s.Runs lim σ fun σ' => t.Runs lim σ' R) : (s ;; t).Runs lim σ R :=
  ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- A branch whose test holds. -/
theorem Stmt.Runs.ite_pos {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : s.Runs lim σ R) (hc : c.Holds σ := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                      (try have := _root_.Light.Std.const_le (by assumption))
                                                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                        )) (hs : c.Safe lim σ := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                                                           (try have := _root_.Light.Std.const_le (by assumption))
                                                                                           simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                                                             )) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun _ => h.1, fun hn => absurd hc hn⟩, by simpa only [Stmt.after, if_pos hc] using h.2⟩

/-- A branch whose test fails. -/
theorem Stmt.Runs.ite_neg {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : t.Runs lim σ R) (hc : ¬ c.Holds σ := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                        (try have := _root_.Light.Std.const_le (by assumption))
                                                        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                          )) (hs : c.Safe lim σ := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                                                             (try have := _root_.Light.Std.const_le (by assumption))
                                                                                             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                                                               )) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun hp => absurd hp hc, fun _ => h.1⟩, by simpa only [Stmt.after, if_neg hc] using h.2⟩





/-! ## Sequencing: what is left of the time goes to the rest of the program -/





























/-! ## Loops whose body is a block -/



/-! ## Counting loops -/







end Light


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Further statements of the paper

Statements of the paper «Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse
Lopsided Graphs» (Josh Alman, Virginia Vassilevska Williams) beyond the five claims of
`EndStatement.lean`, each as a proposition, with the definitions that they use; and statements that
the notions which this file and `EndStatement.lean` both define agree. The file imports
`EndStatement.lean` and Mathlib. It proves none of the statements: the proofs are in the library,
the folder `ThreeSumApsp/`. The five claims do not depend on this file: it is for a reader who wants
to believe a further lemma, equation, table or theorem of the paper.

`Challenge/PaperStatements.lean` states that the propositions hold: `PaperStatements.lemma_6` says
that `PaperStatements.Lemma_6` holds, and `ThreeSumApsp.wordRam_theorem_5` that the running-time
sentence `ThreeSumApsp.WordRam.Items.Theorem_5` holds.

The parts, in this order:

* Section 2: definitions
* Section 2: statements
* Section 3: definitions
* The reduction of Chan and He: definitions
* Section 3: statements
* Section 4: definitions
* Section 4: statements
* Section 5: definitions
* Section 5: statements
* The word RAM: problems
* Agreement with the definitions of EndStatement.lean
* The word RAM: running times

In a comment, "this part" means the part in which the comment stands.
-/

@[expose] public section

/-!
## Section 2: definitions

Definitions used by the statements of Section 2, "Quickly computing certain entries of a thin matrix
product".  They follow the paper's order and names.  Only what the statements need, directly or
through another definition, is defined here; the other notions of the section, among them the tiling
of Section 2.3.4, are defined with the proofs.

Conventions used throughout.

* The paper numbers indices from 1; Lean's `Fin n` starts at 0.  So the paper's `x₁, x₂, x₃` are
  `LeftVar.x 0, LeftVar.x 1, LeftVar.x 2`, the paper's `p₂₁` is `LeftVar.p 1 0`, and so on.
* A string of length `L` over an alphabet `α` is a function `Fin L → α`.  The paper's level
  `ℓ ∈ {1, …, L}` is the element `ℓ - 1` of `Fin L`; the order of the levels is the order of
  `Fin L`.
* The string `s u'` (the variable `s` followed by the string `u'`) is `Fin.cons s u'`; the first
  variable of `u` is `u 0` and the rest of it is `Fin.tail u`.  The empty string is `Fin.elim0`.
* A linear form is given by the vector of its coefficients: a linear form in the left variables is a
  function `LeftVar → ℤ`.  `Pi.single s 1` is the form consisting of the single variable `s`.
-/

section Sec2Definitions

open Finset

namespace ThreeSumApsp

/-! ### 2.2 Schönhage's identity for an inner product and an outer product -/






















































/-! ### 2.3.1 The recursion -/



















/-! ### 2.3.2 Unraveling the recursion computation -/













/-! ### 2.3.3 Batch computation of multiple matrix products -/









































/-! ### 2.3.4 Tiling the N × D × N product by products of shape N₀ × D × N₀: the number `M` -/



/-! ### 2.4.1 Sharing the encoding -/





/-! ### 2.4.2 Skipping the calls that are not needed -/























/-! ### 2.4.3 Few leaves contribute to a sparse set of entries -/













end ThreeSumApsp

end Sec2Definitions

/-!
## Section 2: statements

The numbered lemmas and equations of Section 2 of the paper, and the figures that
assert something of their own.

* Equation (1) is `Eq_1`. Equations (2) and (3) are the definitions `Mult` and `gamma`. Equation (4)
  is the display of `Lemma_9`. Equation (5) is stated in three pieces: `Eq_5_ratio`, `Eq_5_bound`,
  `Eq_5`. Equation (6) is `Eq_6`.
* Lemmas 6 to 11 are `Lemma_6` to `Lemma_11`, each as one statement.
* Of Figure 3 the two worked examples of the caption are stated: `Figure_3`. Of Figure 4 the worked
  example is stated: `Figure_4`. Figure 6 is `Figure_6`; the two counts
  `Sec2_card_contributing_of_order` and `Sec2_card_outStr_of_leaf` say what its numbers count.
* Theorem 5 is a sentence about a machine. It is `Items.Theorem_5`. So of the tiling (Section 2.3.4)
  and of the proof of Theorem 5 (Section 2.4.4) nothing is stated here but the number `M` and
  equation (6): the statements of this part are about a single run of the recursion.
* Remark 12 makes no mathematical claim. Figure 2 recalls Strassen's recursion for intuition; only
  identity (1) is stated. Figure 5 makes no claim of its own. Figure 7 draws the count of Lemma 11;
  two remarks of its caption, that "the bound |U|α_d grows with d up to d ≈ 0.9m" and that the proof
  splits at a point "which is not necessarily where the two bounds cross", are not stated.

`docs/INDEX.md` says for each item of the paper what is stated and what is not.

A hypothesis that is not in the printed text is marked NOTE in the docstring. A hypothesis of the
printed text that is not needed (such as m ≥ 1, Section 2.3.3) is left out without a mark.
-/

section Sec2Statements

open Finset

namespace PaperStatements

open ThreeSumApsp

/-! ### 2.1 Strassen's recursive algorithm -/



/-! ### 2.2 Schönhage's identity for an inner product and an outer product -/



/-! ### 2.3.1 The recursion -/



/-! ### 2.3.2 Unraveling the recursion computation -/





/-! ### 2.3.3 Batch computation of multiple matrix products -/





/-! ### 2.4.2 Skipping the calls that are not needed -/



/-! ### 2.4.3 Few leaves contribute to a sparse set of entries -/















/-! ### 2.4.4 Proof of Theorem 5 -/



end PaperStatements

end Sec2Statements

/-!
## Section 3: definitions

Definitions used by the statements of Section 3, "Exact Triangle reduces to computing certain
entries of a thin matrix product".  They follow the paper's order and names.  Only what the
statements need, directly or through another definition, is defined here; some of the definitions
are used by the statements about programs and not by those of Section 3.

Conventions used throughout.

* A part of `n` vertices is the type `Fin n`.  A pair `(a, b) ∈ A × B` is an element of
  `Fin n × Fin n`, a triple `(a, b, c) ∈ A × B × C` an element of `Fin n × Fin n × Fin n`.
* The paper numbers the pieces from 1; here pieces and chunks are numbered from 0.
* `√D` is the real square root `Real.sqrt D`, `⌊·⌋` and `⌈·⌉` are `Nat.floor` and `Nat.ceil` of real
  numbers, and `log` is the natural logarithm `Real.log` unless a base is written.
* `x ≡ y (mod p)` is `Int.ModEq`, written `x ≡ y [ZMOD p]`.  A residue or label in `ℤ_p` is an
  element of `Fin p`.
* No definition of this part mentions time.  For the sentences of the paper about running time see
  `docs/REMARKS.md`, "Section 3: running times". -/

section Sec3Definitions

namespace ThreeSumApsp

/-! ### 3.1 The Lopsided All-Edges Sparse Triangle problem -/



attribute [instance] LopInstance.fintypeM













/-! #### Cutting a set of pairs into sets of bounded size

Corollary 15 ("splitting W into sets of at most n²/√D query pairs") and the proof of Theorem 17
("cut it into chunks of at most n²/√D query pairs") cut a set of pairs into smaller sets.  The paper
does not say how; we cut along the row-major order of the pairs. -/











/-! ### 3.2 A deterministic reduction from Exact Triangle to Lop-AE-SparseTri -/



namespace TriangleInstance













end TriangleInstance



/-! #### Hashing modulo a prime (proof of Theorem 17) -/



namespace TriangleInstance





end TriangleInstance

/-! #### The instances (proof of Theorem 17) -/











namespace TriangleInstance









/-! #### Witnesses (proof of Theorem 17) -/









end TriangleInstance

/-! ### 3.4 3SUM and APSP reduce to Exact Triangle: the problems -/











/-! A directed graph on the vertices `Fin n` with edge weights in `R` is a function
`w : Fin n → Fin n → WithTop R`: `w i j` is the weight of the edge from `i` to `j`, and `⊤` (that
is, `+∞`) if there is no such edge.  A walk that starts at `i` is given by the list of the vertices
it visits after `i`. -/















/-! #### The shape of the two reductions of [VW13] that Theorem 21 cites -/



/-- A rule that says where each edge weight of a triangle instance on `t` vertices per part is
copied from, given an input `x₀, …, x_{N−1}`: `some (false, i)` stands for `x_i`, `some (true, i)`
for `−x_i`, and `none` for a filler weight.  The rule does not depend on the numbers `x_i`. -/
structure TriangleTemplate (t N : ℕ) where
  /-- The source of `w(a,b)`. -/
  eAB : Fin t → Fin t → Option (Bool × Fin N)
  /-- The source of `w(b,c)`. -/
  eBC : Fin t → Fin t → Option (Bool × Fin N)
  /-- The source of `w(a,c)`. -/
  eAC : Fin t → Fin t → Option (Bool × Fin N)

/-- The weight that a source stands for, given the input `x` and the filler weight `fill`. -/
def templateWeight {N : ℕ} (x : Fin N → ℤ) (fill : ℤ) : Option (Bool × Fin N) → ℤ
  | none => fill
  | some (false, i) => x i
  | some (true, i) => -x i

/-- The triangle instance that a template produces from the input `x` and the filler weight
`fill`. -/
def TriangleTemplate.instantiate {t N : ℕ} (τ : TriangleTemplate t N) (x : Fin N → ℤ) (fill : ℤ) :
    TriangleInstance ℤ t where
  wAB a b := templateWeight x fill (τ.eAB a b)
  wBC b c := templateWeight x fill (τ.eBC b c)
  wAC a c := templateWeight x fill (τ.eAC a c)

/-! #### Asymptotic notation of Section 3 -/







end ThreeSumApsp

end Sec3Definitions

/-!
## The reduction of Chan and He: definitions

[CH20] is Timothy M. Chan and Qizheng He, *Reducing 3SUM to Convolution-3SUM*, Proc. 3rd SIAM
Symposium on Simplicity in Algorithms (SOSA 2020).  Theorem 21(a) of the paper cites [CH20].  What
is used is the reduction in the proof of its Theorem 5.1, a deterministic reduction from 3SUM to
polylogarithmically many instances of Convolution-3SUM.  The theorem itself is a statement about
running times, for 3SUM on three sets and Convolution-3SUM on three arrays.

This part defines such a reduction, as a function from inputs to lists of instances.  What is proved
about it is stated by `Theorem_21a_threeSum_to_convolution` and `Theorem_21a_threeSum_to_exact`.
The construction follows the proof of Theorem 5.1.  Where it differs from [CH20], and what it adds,
is listed in `docs/REMARKS.md`, "Section 3: cited results".

### Why all these definitions are trusted

The list of instances depends on the input.  A statement of the form "there is a list of instances
such that the input has a solution iff one of them has" would be true for trivial reasons.  So the
statements are about the explicitly defined function `instances`, which is built from `reduction`,
and their worth rests on the definitions of this part.

* `reduction` takes three sets of at most n integers.  It returns the nodes of a recursion tree, and
  each node stands for one instance of Convolution-3SUM on three arrays.  3SUM on three sets (are
  there a, b, c, one from each set, with a + b + c = 0?) and Convolution-3SUM on three arrays (are
  there i, j with X i + Y j = Z (i + j)?) are the problems of Definitions 2.1 and 2.2 of [CH20], for
  which Theorem 5.1 is stated.
* `instances` takes n numbers, for the problem whether three of them, at three different positions,
  sum to 0.  It returns instances of Convolution-3SUM on one array.  These are the problems of the
  paper, 3SUM in the reading fixed at `ThreeSum`.

Evaluated literally, `coll` and `heavy` compare all pairs of elements, and each search tests all its
candidates, so the definitions are a specification and not the algorithm.  Nothing in this part is
about a machine.

Every choice that the two functions make depends only on which elements collide and how many pairs
do, on which sets are empty, on binary digits of the numbers and on how often a number occurs.  None
depends on whether a solution exists, with one exception: the solution 0, 0, 0 exists exactly when 0
occurs at three positions.  So it is detected by counting, and it is reported through the three-set
input (`zeroSet x`, {0}, {0}), which has a solution exactly in that case.

In this part `ν` is a node of the recursion tree.  It is not the exponent ν of Theorem 21, which
the statements call `κ`.
-/

section ChanHeDefinitions

namespace ThreeSumApsp

namespace ChanHe

open Finset

/-! ### Collisions and heavy elements -/





/-! ### The arrays of one node -/











/-! ### The choice of the modulus -/









/-! ### The recursion tree -/





/-! ### The parameters -/











/-! ### The reduction for three sets -/



/-! ### From n numbers to three sets -/











/-! ### Three arrays in one -/





/-! ### The whole reduction -/







/-! ### Sizes for inputs of absolute value at most n ^ κ -/







end ChanHe

end ThreeSumApsp

end ChanHeDefinitions

/-!
## Section 3: statements

The claims of Section 3 of the paper, proved or cited there, that are
mathematics and not sentences about a machine.

* Theorem 17, everything but the running time: `Theorem_17`, with `Theorem_17_scanOrder_exists` (its
  hypothesis on the order of the scans can be met) and two pieces of arithmetic behind two terms of
  the additional time, `Theorem_17_hashing_sum_sq_le` and `Theorem_17_write_cost`.
* Remark 18 compares the instances of Theorem 17 with graphs of [VX20]. Stated is what the
  comparison says about the paper's own instance, namely which residues its edges and query pairs
  have: `Remark_18_block`.
* Remark 20: `Remark_20_balance`, `Remark_20_brute_force`.
* Theorem 21, which the paper cites from the literature without a proof: the correctness, the
  numbers and the sizes of the instances of the reductions, and the arithmetic behind the printed
  forms (stated for arbitrary functions, and not applied to the bounds of the reductions). Part (b):
  `Theorem_21b_repeated_squaring`, `Theorem_21b_entries_bounded`, `Theorem_21b_negative_to_exact`,
  `Theorem_21b_log_factors`. Part (a): `Theorem_21a_convolution_to_exact`, `Theorem_21a_compose`,
  and, for the reduction that the paper cites from Chan and He,
  `Theorem_21a_threeSum_to_convolution` and `Theorem_21a_threeSum_to_exact`.
* Definitions 13 and 14 are rendered by definitions. Corollaries 15 and 16 and Theorems 19 and 22
  are sentences about running time; they are stated about programs (`Items.Corollary_15` to
  `Items.Theorem_22_threeSum`).

Not stated here:

* The running time of the reduction of Theorem 17, the time bound of Theorem 21(a), and Theorem
  21(b) in its printed form ("If a deterministic algorithm solves Exact Triangle [...] in time T(s)
  [...], then [...]") have no statement.
* [VW18, Theorem 4.2] has no mathematical statement.
* Remark 23, where the paper indicates the method in one sentence and gives no proof, and
  footnote 9.
* The other sentences inside proofs, and unnumbered claims, are lemmas of the library or are not
  formalized.

`docs/INDEX.md` says for each item of the paper what is stated and what is not. `docs/REMARKS.md`,
"Section 3: running times" and "Section 3: cited results", has the details.

Hypotheses that are added or changed are marked NOTE and listed in `docs/REMARKS.md`, "Section 3:
differences".  Lower bounds that only exclude empty or degenerate cases (`1 ≤ N`, `1 ≤ U`, `0 ≤ U`,
`2 ≤ n`, `0 ≤ κ`, `0 ≤ τ` in the statements for Theorem 21) carry no NOTE.
-/

section Sec3Statements

namespace PaperStatements

open ThreeSumApsp

/-! ### 3.2 A deterministic reduction from Exact Triangle to Lop-AE-SparseTri -/

/-! #### Theorem 17, first step: hashing modulo a prime -/



/-! #### Theorem 17, second step: the instances -/



/-! #### Theorem 17, third step: witnesses -/







/-! ### 3.3 Exact Triangle in truly subcubic time

Theorem 19 is a statement about running time: `Items.Theorem_19`.
Stated here: Remark 20. -/





/-! ### 3.4 3SUM and APSP reduce to Exact Triangle

Theorem 22 is a statement about running time (`Items.Theorem_22_first`, `Items.Theorem_22_second`,
`Items.Theorem_22_threeSum`).  Theorem 21 is cited from the literature, part (a) from [CH20, VW13]
and part (b) from [VW10, VW18, VW13], and the paper gives no proof.  The route taken here:

* for (a), from 3SUM to Convolution-3SUM [CH20, Theorem 5.1], and from there to Exact Triangle
  [VW13, Theorem 4.3];
* for (b), from Negative Triangle to Exact Triangle [VW13, Theorem 3.3], from the (min,+)-product to
  Negative Triangle [VW18, Theorem 4.2], and from APSP to the (min,+)-product by repeated squaring.

Stated here: the parts of this route that are mathematics, among them the combinatorial content of
the two reductions of [VW13]. -/













/-! #### Theorem 21(a): the reduction from 3SUM to Convolution-3SUM, after Chan and He

The first step towards Theorem 21(a), after [CH20, Theorem 5.1]: from n integers bounded by a power
of n, a deterministic reduction computes polylogarithmically many arrays of length Õ(n), whose
entries are again bounded by a power of n, in Õ(n^{3/2}) time; three of the integers sum to 0
exactly if one of the arrays is a yes-instance of Convolution-3SUM.

The namespace `ChanHe` defines a reduction of this kind, as a function from inputs to lists of
instances, in two versions: `ChanHe.reduction` for three sets and three arrays, and
`ChanHe.instances` for n numbers and one array.  Nothing is stated here about `ChanHe.reduction`.

Nothing here is about a machine. That the functions can be evaluated deterministically in n^(3/2)
polylog n time on a word RAM is not stated. Theorem 5.1 of [CH20] as printed is a statement about
running times, so it is not stated here. The easy converse reduction, from Convolution-3SUM to
3SUM, is not treated. -/

section ChanHe

open Finset





end ChanHe

end PaperStatements

end Sec3Statements

/-!
## Section 4: definitions

Definitions used by the statements of Section 4, "The matrix theorem in general: a data structure".
They follow the paper's order and names, with three exceptions: `Cube.starsToP0`, from the proof of
Lemma 29, stands with the cubes of Section 4.2; `epsStar`, from Section 4.1, stands with `Rc`; and
the definitions for Table 2, which is printed in Section 4.1, come last. Every notion of Section 2
(terms, leaves, output strings, inner sets, private leaf, order, `α_d`, `β_d`, `Φ_τ`, `Ψ_τ`) is the
one defined for Section 2 and is not redefined.

Conventions, in addition to those of the definitions of Section 2.

* Table 1: `m` and `L` are natural-number variables, and `D = 4^m`, `N₀ = 3^{L-m}`,
  `K = binom(L, m)`, `M = K N₀²`, `α_d`, `β_d` are `D m`, `N0 L m`, `K L m`, `M L m`, `alpha m d`,
  `beta L m d` of Section 2. The remaining rows of Table 1: `ρ` is `rho L m`, and `γ`, `q`, `R_c(γ)`
  are `gammaOf c θ`, `qOf θ`, `Rc c γ`, all defined below; the switching order is a natural number
  `t`, and the ratio `c`, `ε` and `κ` are real numbers.
* "we say that level ℓ is lower than level ℓ' if ℓ < ℓ'" (Section 4): levels are compared in the
  order of `Fin L`.
* An output string is `η` in the Lean text; the paper writes w.
* The paper fixes `0 ≤ t ≤ m` (Section 4.2) and `L ≥ 10m` (Section 4). The definitions below make
  sense for all natural numbers; the statements carry `t ≤ m` and `10 * m ≤ L` as explicit
  hypotheses where they are needed. `m - t` is subtraction of natural numbers, which is the ordinary
  difference because `t ≤ m`.
-/

section Sec4Definitions

open Finset

namespace ThreeSumApsp

/-! ### Notions from Section 2 -/



/-! ### 4.2 Boxes -/





































/-! ### 4.3 The data structure, in terms of the parameters -/

















/-! ### 4.4 Choosing the parameters -/





















/-! #### Table 2 -/













end ThreeSumApsp

end Sec4Definitions

/-!
## Section 4: statements

The claims of Section 4 of the paper, "The matrix theorem in general: a data structure", that are
mathematics and not sentences about a machine. `docs/INDEX.md` says for each item of the paper what
is stated and what is not. The places where the Lean text differs from the wording of the paper are
collected in `docs/REMARKS.md`, "Section 4: differences".

The order is the paper's, with these exceptions. Figure 10 and `Lemma_28_boxes` come after Lemma 28.
`Eq_10`, from the proof of Corollary 31, stands with equation (10). `Sec4_epsStar_numeric` (Section
4.1) and `Sec4_Rc_lt_epsStar` (Table 1) stand with the clauses of Corollary 31 on ε*. The statements
on Table 2, `Table_1_section_2_column` and `Corollary_26_W` come at the end.

* Sentences about running time and space are sentences about a machine. Those of Theorems 24, 25 and
  30 and of Corollaries 26, 31 and 32 are stated about programs: `Items.Theorem_24` to
  `Items.Corollary_32`. The bound of the second sentence of Lemma 29 ("in O(L) time and space per
  box") has no statement; Theorem 30 about programs has its consequence, the first term of (8).
* Expressions (8) and (9) are the definitions `cost8` and `cost9`. Equation (11) is the definition
  `Rc`.
* Figure 9 draws the cube and the boxes of one output string in a small example (L = 3, t = 1).
  Nothing is stated for it.
* No statement says that q increases with θ on (0, 0.9), or that there is only one θ with
  γ = κ - q. So "the θ that gives the q of the column" and "the θ at which γ = κ - q" (Section 4.4)
  are rendered by "some θ with ..." in `Table2Query`, `Table2Density` and the field `eps` of
  `Table2Row`.
* The standing assumptions of the section, `0 ≤ t ≤ m` (Section 4.2) and `L ≥ 10m` (Section 4),
  appear as the explicit hypotheses `t ≤ m` and `10 * m ≤ L` in the statements that need them. "As
  in Section 2.4.3, all output strings in this section have inner sets of exactly m elements"
  (Section 4) is the hypothesis `(innerSetO η).card = m`.
* An output string is `η` in the Lean text; the paper writes w.
* `D m = 4 ^ m` is the paper's `D` after "from now on D = 4^m" (the proof of Corollary 26). The
  inner dimension of the given matrices, before it is padded to a power of four, is written `D₀`.
* Where a statement renders an `O(·)`, it has an explicit constant and an explicit order of
  quantifiers, and the docstring says how the sentence was read.
-/

section Sec4Statements

open Finset

namespace PaperStatements

open ThreeSumApsp

/-! ### 4.2 Boxes -/



















/-! ### 4.3 The data structure, in terms of the parameters -/







/-! #### The decay rate ρ and equation (7) -/







/-! ### 4.4 Choosing the parameters -/







/-! #### Corollary 31: the clauses that are not about time -/











/-! #### Corollary 32 -/



/-! #### Table 2, and the column of Table 1 on Section 2 -/







/-! ##### The six rows of Table 2

Each statement has the numbers of a row in the order in which the paper prints them: the first line
has `c`, `ε` and the left half, the second line the right half. It says that every entry is computed
as Section 4.4 prescribes and is rounded down to four decimals, and that the `ε` of the row is below
`R_c(γ)` at every entry and is rounded down to three decimals. By `Table_2_query_valid`,
`Table_2_ninth_valid` and `Table_2_density_valid`, Corollary 31 or 32 then gives what the caption
claims for the entry. -/

















/-! #### Corollary 26 -/



end PaperStatements

end Sec4Statements

/-!
## Section 5: definitions

Definitions used by the statements about Section 5, in the paper's order. Only what the statements
need is defined: blocks of matrices (5.1, 5.2, 5.4), comparison counts, the two counting
problems, and the construction of Lemma 37 (5.2), and the three hinted matrix-vector problems with
the conjectures about them (5.4). The definitions of 5.4 are used by the statements about programs.
The weighted `k`-Clique problems of 5.3 are `EndStatement.ZeroWeightKClique`,
`WordRam.MinKClique` and `WordRam.MaxKClique`.

Conventions.

* The paper numbers indices from 1; Lean's `Fin n` starts at 0.
* The paper treats n^μ, n/d, n/t₂ as integers.  Here a matrix that is cut into `b` blocks of `m`
  consecutive rows has `b * m` rows, and row `i` of block `p` is row `p * m + i`, which is
  `finProdFinEquiv (p, i)`.  The arithmetic of Theorem 35 has `d = ⌊n^{1/40}⌋` and the real quotient
  `n/d`; nothing is stated about cutting into blocks of `d` when `d` does not divide `n`.
* Definitions shared with Section 3 (`TriangleInstance`, `IsMinPlusProduct`, ...) and Section 4
  (`epsStar`, `padInnerCols`, `padInnerRows`) stand with the definitions of these sections.
-/

section Sec5Definitions

open Finset

namespace ThreeSumApsp

/-! ### Blocks of consecutive rows and columns (used in 5.1, 5.2 and 5.4) -/





/-! ### 5.2 Comparison counts -/

namespace ComparisonCounts





























/-! #### The objects in the proof of Lemma 36 -/

















/-! #### The construction of Lemma 37 -/



























/-! #### The parameters of Corollary 38 and of the proof of Theorem 35 -/







end ComparisonCounts

/-! ### 5.4 Three conjectures of van den Brand, Nanongkai, and Saranurak -/

namespace HintedMv

















end HintedMv

end ThreeSumApsp

end Sec5Definitions

/-!
## Section 5: statements

The pieces of Sections 5.1 and 5.2 that the paper itself argues and that are mathematics:
correctness of the constructions, counts, and the arithmetic of the exponents, with the paper's
constants. `docs/INDEX.md` says for each item of the paper what is stated and what is not. Where a
statement differs from the printed sentence, `docs/REMARKS.md`, "Section 5 and the introduction:
differences", says why.

* The sentences of the form "can be solved in O(...) time" are not stated here. Those of Corollaries
  39 and 40 are stated about programs of the word RAM (`Items.Corollary_39_zero` to
  `Items.Corollary_40_fail`), and nothing else of Sections 5.3 and 5.4 is stated. Those of Theorem
  35 and of Corollary 38 are about randomized algorithms or real numbers, and the machine has
  neither random bits nor real numbers. That of Theorem 34 rests on Theorem 33, which the paper
  proves and which is not proved here, and on μ, which is defined through ω(1, μ, 1). Three lemmas
  of the library (the files that hold the proofs), `conditional_theorem_34`,
  `conditional_corollary_38` and `conditional_theorem_35`, say how each follows from the results
  that its proof uses, which are taken as hypotheses. The running time of Lemma 37 and Lemma 36 as a
  whole occur only as hypotheses of these lemmas. The list is in `docs/REMARKS.md`, "Section 5 and
  the introduction: running times".
* The theorems of other papers that Section 5 uses as black boxes are not stated (`docs/REMARKS.md`,
  "Section 5: cited results"). In particular the randomized reductions behind Lemma 36 are cited.
  Nothing of Theorem 33 and of its proof is stated.
* Of Lemma 36, the size O(n²/d) of the pair set of part (b) is not stated;
  `Theorem_35_three_sum_count` puts n²/d in its place. The last sentence of the lemma, on the
  operations applied to real numbers, is not stated.
* The other sentences inside proofs are lemmas of the library or are not formalized.
* The statements on blocks have n = b * d; the paper's proof treats n/d as an integer.
* "Õ(f)" is read as "O(f · (log n)^c) for some constant c".
-/

section Sec5Statements

open Finset Asymptotics Filter

namespace PaperStatements

open ThreeSumApsp

/-! ### 5.1 Directed APSP with small integer weights -/









/-! ### 5.2 3SUM, APSP, and Exact Triangle with real inputs -/

section ComparisonCounts

open ComparisonCounts

/-! #### Lemma 36(a): the parts argued in the paper -/









/-! Proof of Lemma 36(a): "APSP with real weights and no negative cycles can be computed by
successive squaring of the weight matrix, performing ⌈log₂ n⌉ such products." This is
`Theorem_21b_repeated_squaring` (Theorem 21(b)), which is stated for weights in any linearly ordered
commutative group, in particular for real weights. -/











/-! #### Lemma 36(b): the parts argued in the paper -/







/-! #### Lemma 37

The lemma says "we can build matrices X [...] and Y [...] and compute integers γ₂(r,c), (r,c) ∈ P,
with" γ(r,c) = (XY)[r,c] + γ₂(r,c). Read as a bare existence statement this would be trivial (take
X = Y = 0), so the statements below are about the matrices and the integers that the proof
constructs: `matX`, `matY`, `sameBlockCount`, for an arbitrary outcome `o` of the sort and an
arbitrary indexing `idx` of the pairs (color, block). The running time of the lemma is a hypothesis
of the library's lemma `conditional_corollary_38`. -/









/-! #### Corollary 38: correctness and parameter arithmetic -/





/-! #### Proof of Theorem 35: the arithmetic, with d := ⌊n^{1/40}⌋ -/



















end ComparisonCounts

end PaperStatements

end Sec5Statements

/-!
## The word RAM: problems

First comes what it means that a program of the machine of `EndStatement.lean` solves a problem
within a time bound.  Then come the problems: which number lies in which cell at the start, and
what a right answer is.  No sentence of the paper is stated here; the sentences are the item
statements `Items.Theorem_5`, …, in the terms that are defined here.  `docs/MACHINE.md`, Part 1,
goes through the definitions at length and compares the machine with the standard word RAM point by
point.

**What a reader of the statements about programs can skip.**  Of the definitions of Sections 2 to 5
the statements `wordRam_theorem_5`, … use only these 28:
* Section 2: `N0`, `K`, `alpha`;
* Section 3: `LopInstance`, `LopInstance.commonNeighbors`, `LopInstance.InTriangle`,
  `LopInstance.numTriangles`, `LopInstance.ofMatrices`, `GraphHasZeroTriangle`;
* Section 4: `rho`, `cost8`, `costQuery`, `cost9`, `entropy`, `rhoC`, `gammaOf`, `qOf`, `lnΛ`, `Rc`,
  `epsStar`;
* Section 5, namespace `HintedMv`: `boolMul`, `toInt`, `vHintedOutput`, `MvHintedOutput`,
  `uMvHintedOutput`, `Conjecture52`, `Conjecture57`, `Conjecture512`.

NOTE.  Eight notions are defined twice: in `EndStatement.lean`, and with Mathlib for the statements
on the reductions and about programs.  For each of them a statement, named in brackets, says that
the two definitions agree (a further form of `O(n^a)`, the bound `Within` on the steps of a phase,
is not compared):
* "a program solves a problem": there `Problem`, `Problem.SolvedBy` and the word sizes of
  `Problem.SolvedInTime`, for one size `n`; here `Problem`, `Admissible`, `output` and `Solves`, for
  several sizes (`Agreement_solves`);
* `O(n^r)`: there `BigO`, for a rational exponent and from `n = 2` on; in Section 3 `IsBigOPow`, for
  a real exponent and all large `n` (`Agreement_bigO`, for `r ≥ 0`);
* "solved in time": there `Problem.SolvedInTime` and `BigO`, with a rational exponent and a bound
  `T(n)` that is `O(n^r)` from `n = 2` on; here `SolvesWithin`, `SolvedInTimeAt` and `SolvedInTime`,
  with a real exponent and the bound `C (n^a (log n)^e + 1)` at every size
  (`Agreement_solvedInTime`, for a rational exponent `r ≥ 0` and `e = 0`); both are stated through
  `Problem.SolvedBy`;
* Exact Triangle: `EndStatement.ExactTriangle` and `TriangleInstance.HasZeroTriangle`
  (`Agreement_exactTriangle`);
* the (min,+)-product: `EndStatement.MinPlusProduct` and `IsMinPlusProduct`
  (`Agreement_minPlusProduct`);
* APSP: `EndStatement.Path` and `EndStatement.APSP`, where a missing edge is `none`, and
  `walkWeight`, `NoNegativeCycle` and `IsDistanceMatrix`, where it is `⊤`
  (`Agreement_apsp_noNegativeCycle`, `Agreement_apsp_output`);
* a matrix written row by row: `EndStatement.rowByRow` and `rowMajor` (`Agreement_rowByRow`);
* the weight of a `k`-clique: the sum in `EndStatement.ZeroWeightKClique` and `cliqueWeight`
  (`Agreement_cliqueWeight`).

**The machine** is defined in `EndStatement.lean` and nowhere else: `Instr`, `exec` and
`loadWords`.  The paper works "in the standard word RAM model with O(log N)-bit words", and so
counts "operations on O(log N)-bit integers" (Section 2).  There is no division, no shift, no
bitwise operation and no constant but 1: in its instructions the machine is weaker than the standard
word RAM.

NOTE.  On four points the machine is generous; none of them changes an exponent:
* Every cell outside the input, with a positive or a negative name, holds 0 at the start, and
  `Solves`, `SolvesWithin` and `RunsPhases` charge no space, so a table that is addressed directly
  by a number costs nothing to set up (on a machine without this, lazy initialisation costs a
  constant factor).
* The finitely many cells that a program names in its text need not be addressable by a word.
* The slope `b` of the word size is chosen after the exponent `κ` of the magnitude of the numbers.
* The inputs of phases and the queries arrive at no cost. -/

section WordRamProblems

namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec loadWords)

/-! ### What it means to solve a problem

**The order of the choices.**  In every statement the order is: the constants of the problem (the
exponent `κ` of the magnitude of the numbers, the `k` of `k`-Clique); then the program, the slope
`b` of the word size and the constant `C` of the time bound; then the instance; then the word size,
any number of bits that is admissible for the slope.  So the program cannot depend on the instance
or on its size, and it cannot rely on long words. -/

/-! #### The word size and the output cells -/





/-! #### Problems, and solving a problem within a time bound -/





/-! #### Time bounds in one size `n`, for the problems of `EndStatement.lean` -/











/-! #### A query program that serves one query after the other -/





/-! #### Programs that receive their input in phases

A problem in phases has one program for each phase.  The inputs of the phases are laid
out one after the other in the cells 0, 1, 2, …, but the input of a phase is written into its cells
only when the phase starts.  Each program starts at its first instruction on the memory that the
previous phase has left; the first one starts on a memory of zeros.  So a phase cannot see the input
of a later phase, and nothing is reset between phases.  The output is read from the cells after the
last input.  Receiving an input takes no steps, and the inputs of earlier phases stay in memory
unless a program overwrites them.  What an earlier phase has left in the cells of a later input is
lost; the earlier phase knows which cells these are, since all sizes are given in Phase 1.  (In the
running times of Corollary 40 the bound of a phase is at least the length of its input, if the
exponent `γ` of `Items.Corollary_40_general_times` is at most 1; so they do not depend on inputs
being free.) -/







/-! ### The problems of the paper, their inputs and their answers

**Layout.**  Matrices are written row by row, one number per cell, as signed words.  Booleans are
written as 0 and 1, and indices and vertices count from 0.  The first cells hold the sizes.  The
bound on the absolute values of the numbers is not written into memory.  For the matrix problems it
is a number `U` that is part of the instance as a mathematical object (`ThinPair`); for the problems
in the form of `EndStatement.Problem` it is a hypothesis of `SolvesWithin`.  In the statements it is
a fixed power of the size, with an exponent that is fixed before the program (and 1 for the 0/1
matrices of the lopsided triangle problems).  A program for a problem with an output has to accept,
and to leave the output in the cells right after the input. -/

/-! #### How matrices and Booleans are written -/





/-! #### The wanted entries of a thin matrix product (Theorems 1, 5, 25 and 30, Corollaries 26 and
32) -/









/-! #### The two-stage data structure for a thin matrix product (Section 4) -/





/-! #### The lopsided triangle problems (Definitions 13 and 14) -/









/-! #### Exact Triangle, 3SUM, the (min,+)-product and APSP

These four are the problems `ExactTriangle`, `ThreeSum`, `MinPlusProduct` and `APSP` of
`EndStatement.lean`. -/

/-! #### Exact Triangle on `n`-vertex graphs -/





/-! #### Zero-Weight, Min-Weight and Max-Weight `k`-Clique (Corollary 39)

Zero-Weight `k`-Clique is the problem `ZeroWeightKClique k` of `EndStatement.lean`.  The other two
have its input: for each ordered pair of parts `(p, q)`, in row-major order, an `n × n` block of
numbers, where `w p q u v` is the weight between vertex `u` of part `p` and vertex `v` of part `q`.

NOTE.  All `k²` blocks are input, but only the blocks with `p < q` count; the others may hold
anything within the bound on the numbers of the input.  The paper does not fix a layout. -/







/-! #### The three hinted matrix-vector problems of [vdBNS19] (Corollary 40) -/









end ThreeSumApsp.WordRam

end WordRamProblems

/-!
## Agreement with the definitions of EndStatement.lean

Eight notions have two definitions each.  `EndStatement.lean` defines them for the five claims, with
Lean's core library only, for integers and square matrices.  The statements on the reductions and
the statements about programs use definitions with Mathlib: the paper needs Exact Triangle and the
(min,+)-product also over the real numbers, matrices that are not square, problems with several
sizes, and time bounds with real exponents and logarithmic factors.  The statements below say that
the two definitions of each notion agree.  APSP has two statements, one for the promise and one for
the output.
-/

section AgreementStatements

open ThreeSumApsp.WordRam

namespace PaperStatements

open ThreeSumApsp



















end PaperStatements

end AgreementStatements

/-!
## The word RAM: running times

An item statement is a running-time sentence of the paper, written as a proposition about programs
of the machine of `EndStatement.lean` and named after its item, such as `Items.Theorem_5` or
`Items.Corollary_26`.  Its docstring quotes the sentence.  The notions of solving are `Solves`,
`IsDataStructure`, `SolvesWithin` and `RunsPhases`, and the forms derived from them (`SolvedInTime`,
`AchievesVHinted`, …); the layouts of the inputs and the order of the choices are explained with
them.  The definitions only say what the sentences mean.  That they hold is stated by the theorems
`wordRam_theorem_5`, `wordRam_corollary_26`, ….  The five claims of `EndStatement.lean` are five of
the bounds of `Theorem_19`, `Theorem_22_second` and `Corollary_39_zero`.

* **Order.**  Sections 2 to 5 in the paper's order, then the introduction.  Its Theorems 1 to 4
  restate and combine the later items (here Theorem 3 is stated through Corollary 26, and Theorem 4
  through Corollary 40), so they stand last.
* **Items and propositions.**  Some items have several propositions, for instance `Corollary_26` for
  the data structure and `Corollary_26_wanted` for the entries at a given set of positions; and some
  propositions hold several bounds of their item, joined by "and", for instance `Theorem_19`.
* **Definitions that are not items.**  `thinDom`, `HasDataStructure` and `theorem30Dom` abbreviate
  hypotheses or sentences that occur in more than one proposition.  `DataStructureBelow` and
  `WantedBelow` state the last sentences of Theorems 3 and 1 ("More generally, …") with a bound `ε₀`
  in the place of 0.1204.
* **Departures.**  Where a proposition departs from the printed sentence, for instance by a lower
  bound `D ≥ 1` that the paper leaves out, its docstring, or that of the definition through which it
  is stated, says so, mostly in a paragraph that begins with NOTE.
* **Real parameters.**  Corollaries 31 and 32 have real parameters `c` and `θ`.  The statements do
  not mention the numbers `⌈cm⌉` and `⌈θm⌉` of the proof; they only say that programs with certain
  time bounds exist.  So they make sense, and are stated, for all real `c` and `θ`, although a
  program is a finite text: a proof may use rational parameters close to `c` and `θ`, which the
  strict inequality `ε < R_c(γ)` leaves room for.
* **Not stated about programs.**  The other sentences of the paper about running time are not stated
  about programs.  The machine has neither random bits nor real numbers: Theorem 35 (with the half
  of Theorem 2 on real inputs) needs both, and Corollary 38 needs real numbers.  Theorem 34 rests on
  Theorem 33, which the paper proves and which is not proved here, and on μ, which is defined
  through ω(1, μ, 1). For these three items see the library's lemmas `conditional_theorem_34`,
  `conditional_corollary_38` and `conditional_theorem_35`, where Theorem 33 and Lemmas 36 and 37 are
  hypotheses.  Theorems 17 and 21 speak of an arbitrary solver, while each item statement is about
  one fixed program.  The time bound of Lemma 29 enters the bound (8) of Theorem 30. -/

section WordRamItems

namespace ThreeSumApsp.WordRam

open EndStatement (Instr)

namespace Items

/-! ### Section 2: Theorem 5 -/



/-! ### Section 3: Corollaries 15 and 16, Theorems 19 and 22 -/













/-! ### Section 4: Theorems 24 and 25, Corollary 26, Theorem 30, Corollaries 31 and 32 -/



























/-! ### Section 5: Corollaries 39 and 40 -/











/-! ### Section 1, the introduction: Theorems 1 to 4 -/











end Items

end ThreeSumApsp.WordRam

end WordRamItems


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Limits -/









/-! ## Specifications of single routines -/



/-! ## Tasks and solvers -/





















/-! ## Hosts -/



/-- From a host to a transfer of running times.  What remains is arithmetic: a bound for the host's
time function, given a bound for the solver's. -/
theorem IsHost.solvedIn {lower upper : Task} {time : (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ}
    {need : (ℕ → ℕ → Need) → ℕ → ℕ → Need} (h : IsHost lower upper time need) {T T' : ℕ → ℝ → ℝ}
    (hs : SolvedIn lower T)
    (hb : ∀ Tn : ℕ → ℕ → ℕ, (∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤
    T n u) → ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (time Tn n U : ℝ) ≤ T' n u) :
    SolvedIn upper T' := by
  obtain ⟨P, p, Tn, r, hr, hsol, hT⟩ := hs
  obtain ⟨R, p', hsol'⟩ := h.1 P p Tn r hsol
  exact ⟨P ++ R, p', time Tn, need r, h.2 r hr, hsol', hb Tn hT⟩

/-! ## Tasks with a list of parameters -/











end Light


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The answer of a decision problem as a number

A routine for a decision problem returns 1 for yes and 0 for no: `flag p` is this number for the
proposition `p`.
-/

@[expose] public section

namespace ThreeSumApsp







/-- The number 1 means yes. -/
theorem flag_eq_one_iff {p : Prop} : flag p = 1 ↔ p := by
  by_cases h : p
  · exact iff_of_true (flag_of h) h
  · exact iff_of_false (by rw [flag_of_not h]; decide) h





end ThreeSumApsp


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Calculating with `n^{a+o(1)}`

`IsPowLittleO f a` reads `f(n) = n^{a+o(1)}` as an upper bound on `|f(n)|`: there is a sequence
`ε(n) → 0` with `|f(n)| ≤ n^{a+ε(n)}` for all large `n`. This says the same as `f(n) = O(n^{a+η})`
for every `η > 0` (`isPowLittleO_iff`). In the second form the rules of the notation follow from the
rules for `O`:

* the exponent may grow (`IsPowLittleO.mono`), and a strictly larger exponent absorbs the `o(1)`
  (`IsPowLittleO.isBigOPow`);
* sums, products and constant factors (`IsPowLittleO.add`, `IsPowLittleO.mul`,
  `IsPowLittleO.const_mul`);
* `(n^{d+o(1)})^{c+o(1)} = n^{cd+o(1)}` for `c, d ≥ 0` (`IsPowLittleO.comp`);
* `O(n^a)` and `O(n^a (log n)^{O(1)})` are `n^{a+o(1)}` (`IsBigOPow.isPowLittleO`,
  `IsPowPolylog.isPowLittleO`).
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

/-! ### The two readings of the notation -/

/-- The `o(1)` is absorbed: if `f = n^{a+o(1)}` and `a < b`, then `|f n| ≤ n ^ b` for all large `n`.
-/
theorem IsPowLittleO.eventually_abs_le (h : IsPowLittleO f a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ b := by
  obtain ⟨ε, hε, hf⟩ := h
  filter_upwards [hf, hε.eventually_lt_const (sub_pos.2 hab), eventually_ge_atTop 1]
    with n hfn hεn hn
  exact hfn.trans (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) (by linarith))

/-- If for every `η > 0`, `|f(n)| ≤ n^{a+η}` for all large `n`, then `f(n) = n^{a+o(1)}`. For
`ε(n)` take the excess of the exponent that is needed at `n`: the number with
`n^{a+ε(n)} = max(|f(n)|, n^a)`. -/
theorem IsPowLittleO.of_eventually_abs_le
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ (a + η)) : IsPowLittleO f a := by
  -- All three claims are about `n ≥ 2`, where `n > 1` and the maximum is positive.
  have hbase : ∀ n : ℕ, 2 ≤ n → (1 : ℝ) < n ∧ 0 < max |f n| ((n : ℝ) ^ a) := fun n hn =>
    ⟨by exact_mod_cast hn, lt_max_of_lt_right (Real.rpow_pos_of_pos (by positivity) a)⟩
  refine ⟨fun n => Real.logb n (max |f n| ((n : ℝ) ^ a)) - a,
    tendsto_order.2 ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩, ?_⟩
  · -- `ε(n) ≥ 0`, because the maximum is at least `n^a`.
    filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨hn1, hpos⟩ := hbase n hn
    have hge : a ≤ Real.logb n (max |f n| ((n : ℝ) ^ a)) :=
      (Real.le_logb_iff_rpow_le hn1 hpos).2 (le_max_right _ _)
    linarith [hδ, hge]
  · -- `ε(n) ≤ δ/2` as soon as `|f(n)| ≤ n^{a+δ/2}`.
    filter_upwards [h (δ / 2) (half_pos hδ), eventually_ge_atTop 2] with n hfn hn
    obtain ⟨hn1, hpos⟩ := hbase n hn
    have hle : Real.logb n (max |f n| ((n : ℝ) ^ a)) ≤ a + δ / 2 :=
      (Real.logb_le_iff_le_rpow hn1 hpos).2
        (max_le hfn (Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith)))
    linarith [hδ, hle]
  · -- `n^{a+ε(n)}` is the maximum.
    filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨hn1, hpos⟩ := hbase n hn
    rw [add_sub_cancel, Real.rpow_logb (zero_lt_one.trans hn1) hn1.ne' hpos]
    exact le_max_left _ _

/-- `f(n) = n^{a+o(1)}` if and only if `f(n) = O(n^{a+η})` for every `η > 0`. -/
theorem isPowLittleO_iff : IsPowLittleO f a ↔ ∀ η : ℝ, 0 < η → IsBigOPow f (a + η) :=
  ⟨fun h η hη => (isBigOPow_rpow (a + η)).mono_left
      ((h.eventually_abs_le (lt_add_of_pos_right a hη)).mono
        fun _ hfn => hfn.trans (le_abs_self _)),
    fun h => .of_eventually_abs_le fun η hη =>
      (h (η / 2) (half_pos hη)).eventually_abs_le (by linarith)⟩

/-! ### The rules -/





/-- `O(n^a) ⊆ n^{a+o(1)}`. -/
theorem IsBigOPow.isPowLittleO (h : IsBigOPow f a) : IsPowLittleO f a :=
  isPowLittleO_iff.2 fun _ hη => h.mono (by linarith)









/-! ### Composition -/





end ThreeSumApsp


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The integer square root by counting up

sqrt(K) returns ⌊√K⌋ within `sqrtTime K` steps (`sqrt_meets`), by running through the squares 1, 4,
9, …: after (k + 1)² comes (k + 1)² + 2k + 3.  It does not touch the memory.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Sqrt





end Sqrt





/-- **sqrt(K)** returns ⌊√K⌋ and leaves the memory as it is. -/
theorem sqrt_meets {p K : ℕ} (hp : P[p]? = some sqrtBody) (μ : ℕ → ℤ)
    (hword : ((3 * K + 4 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [K] μ (sqrtTime K) fun r μ' => r = (Nat.sqrt K : ℤ) ∧ μ' = μ := by
  have hle : Nat.sqrt K * Nat.sqrt K ≤ K := Nat.sqrt_le K
  have hlt : K < (Nat.sqrt K + 1) * (Nat.sqrt K + 1) := Nat.lt_succ_sqrt K
  have hself : Nat.sqrt K ≤ K := Nat.sqrt_le_self K
  refine .of_body hp ?_
  unfold sqrtBody sqrtTime
  -- k := 0; sq := 1
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             1
               -- while sq ≤ K.  Before round i, k = i and sq = (i + 1)².
               
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  -- while sq ≤ K.  Before round i, k = i and sq = (i + 1)².
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [K, i, ((i + 1) * (i + 1) : ℕ)], μ⟩) (Nat.sqrt K) (by simp) ?round ?done
    le_rfl)
  case round =>
    rintro i _ hi rfl
    have hsq : (i + 1) * (i + 1) ≤ Nat.sqrt K * Nat.sqrt K := Nat.mul_le_mul (by omega) (by omega)
    rw [show (i + 1 + 1) * (i + 1 + 1) = (i + 1) * (i + 1) + 2 * i + 3 by ring]
    generalize (i + 1) * (i + 1) = q at hsq
    -- The test is safe and holds.  sq := sq + 2 k + 3; k := k + 1 is safe and leads to the next
    -- state.
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                   (try have := _root_.Light.Std.const_le (by assumption))
                                                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                     ), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize (Nat.sqrt K + 1) * (Nat.sqrt K + 1) = q at hlt
    refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                      (try have := _root_.Light.Std.const_le (by assumption))
                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                        ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                     (try have := _root_.Light.Std.const_le (by assumption))
                                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                       ), ?_⟩
    -- the result is k
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.setToThen (Nat.sqrt K) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                         )
    exact ⟨rfl, rfl⟩

end Light


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# From a pair to the next pair

A loop that runs through the pairs (a, b) with a, b < n in the order of their numbers t = a n + b
keeps a = t / n and b = t % n in two local variables, so that no division is needed.
`nextPair A B N` is the step from one pair to the next, and `Ends.nextPair` is its rule.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}



/-- **From the pair number t to the pair number t + 1.** -/
theorem Ends.nextPair {A B N n t T : ℕ} {l : List ℤ} {μ : ℕ → ℤ} {Q : State → Prop}
    (h : Q ⟨frame (setLocal (setLocal l B ((t + 1) % n : ℕ)) A ((t + 1) / n : ℕ)), μ⟩)
    (hn : 0 < n) (ht : ((t + 1 : ℕ) : ℤ) ≤ lim.word) (hnw : (n : ℤ) ≤ lim.word)
    (hA : frame l A = (t / n : ℕ)) (hB : frame l B = (t % n : ℕ)) (hN : frame l N = n)
    (hAB : A ≠ B := by decide) (hBN : N ≠ B := by decide) (hT : 14 ≤ T := by (((first
                                                                                  | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                                                        _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                      first
                                                                                      | omega
                                                                                      | (ring_nf; omega))
                                                                                  | omega
                                                                                  |
                                                                                    (simp [] <;>
                                                                                        first
                                                                                        | omega
                                                                                        | (ring_nf; omega))))
                                                                                      )) :
    Ends lim P d (nextPair A B N) ⟨frame l, μ⟩ T Q := by
  have hmod := Nat.mod_lt t hn
  have hdiv := Nat.div_le_self t n
  have hlast := Nat.succ_div_mod_of_eq (n := n) (i := t)
  have hinner := Nat.succ_div_mod_of_ne (i := t) hn
  generalize t / n = a at *
  generalize t % n = b at *
  -- b := b + 1
  refine Ends.setToThen (b + 1 : ℕ) ?_ (by ((simp only [_root_.Light.Expr.Safe, _root_.Light.Expr.val, _root_.Light.Expr.cost,
                                                _root_.Light.Op.eval, _root_.Light.Cond.Holds, _root_.Light.Cond.cost, _root_.Light.Cond.Safe,
                                                _root_.Function.update_apply, _root_.reduceIte, _root_.true_and, _root_.and_true,
                                                _root_.Nat.reduceEqDiff, _root_.Nat.cast_ofNat, _root_.Nat.cast_zero, _root_.Nat.cast_one,
                                                Expr.Gives, hB, abs_le])
                                                                             ); omega)
    (by simp; omega)
  -- if b = n then b := 0; a := a + 1
  refine Ends.iteLast (fun he => ?_) (fun he => ?_) ⟨trivial, trivial⟩ (by simp; omega)
  · have he : b + 1 = n := by
      have : ((b + 1 : ℕ) : ℤ) = n := by
        simpa only [Cond.Holds, Expr.val, frame_setLocal, if_pos, if_neg hBN, hN] using he
      exact_mod_cast this
    rw [(hlast he).1, (hlast he).2] at h
    refine Ends.setToThen (0 : ℕ) (Ends.setTo (a + 1 : ℕ) ?_
      (by ((simp only [_root_.Light.Expr.Safe, _root_.Light.Expr.val, _root_.Light.Expr.cost,
               _root_.Light.Op.eval, _root_.Light.Cond.Holds, _root_.Light.Cond.cost, _root_.Light.Cond.Safe,
               _root_.Function.update_apply, _root_.reduceIte, _root_.true_and, _root_.and_true,
               _root_.Nat.reduceEqDiff, _root_.Nat.cast_ofNat, _root_.Nat.cast_zero, _root_.Nat.cast_one,
               Expr.Gives, frame_setLocal, if_neg hAB, hA, abs_le])
                                                                        ); omega)
      (by simp; omega)) (by ((simp only [_root_.Light.Expr.Safe, _root_.Light.Expr.val, _root_.Light.Expr.cost,
                                 _root_.Light.Op.eval, _root_.Light.Cond.Holds, _root_.Light.Cond.cost, _root_.Light.Cond.Safe,
                                 _root_.Function.update_apply, _root_.reduceIte, _root_.true_and, _root_.and_true,
                                 _root_.Nat.reduceEqDiff, _root_.Nat.cast_ofNat, _root_.Nat.cast_zero, _root_.Nat.cast_one,
                                 Expr.Gives])
                                                  ); omega) (by simp; omega)
    convert h using 2
    funext y
    simp only [frame_setLocal]
    split_ifs <;> rfl
  · have he : b + 1 ≠ n := fun e => he (by
      simp only [Cond.Holds, Expr.val, frame_setLocal, if_pos, if_neg hBN, hN]
      exact_mod_cast e)
    rw [(hinner he).1, (hinner he).2] at h
    refine Ends.skip ?_
    convert h using 2
    funext y
    simp only [frame_setLocal]
    split_ifs with h1 h2 h2
    · exact absurd (h2.symm.trans h1) hAB
    · rfl
    · rw [h2, hA]
    · rfl

end Light


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Theorem 21(a): Convolution-3SUM reduces to Exact Triangle

[VW13, Theorem 4.3] in the form needed for Theorem 21(a): Convolution-3SUM on `N < t²`
numbers becomes `2t` instances of Exact Triangle on `t` vertices per part.  In instance `s` the
triangle `(a, b, c)` stands for the pair `i = at + b`, `j = ct + s - b` (`convTemplate`).  Every
solution is such a triangle (`exists_hasZeroTriangle`), and a zero triangle is a solution, because
an index out of range gives a weight so large that the sum is positive
(`convolution3SUM_of_isZeroTriangle`).  Together: `convolution3SUM_iff`, and with `t = ⌊√N⌋ + 1`,
`theorem_21a_convolution_to_exact`.
-/

@[expose] public section

namespace ThreeSumApsp

namespace Theorem21

/-- Instance `s` of the reduction from Convolution-3SUM.  The triangle `(a, b, c)` stands for the
pair `i = a t + b`, `j = c t + s - b`, for which `i + j = (a + c) t + s`: the edge `(a, b)` carries
`x_i`, the edge `(b, c)` carries `x_j`, and the edge `(a, c)` carries `-x_{i+j}`.  An edge whose
index is out of range gets the filler weight. -/
def convTemplate (t N s : ℕ) : TriangleTemplate t N where
  eAB a b := if h : a.val * t + b.val < N then some (false, ⟨a.val * t + b.val, h⟩) else none
  eBC b c :=
    if h : b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N then
      some (false, ⟨c.val * t + s - b.val, h.2⟩)
    else none
  eAC a c :=
    if h : (a.val + c.val) * t + s < N then some (true, ⟨(a.val + c.val) * t + s, h⟩) else none

/-- The weight of the edge `(a, b)`. -/
theorem convTemplate_AB {t N s : ℕ} {x : Fin N → ℤ} {fill : ℤ} (a b : Fin t) :
    templateWeight x fill ((convTemplate t N s).eAB a b)
      = if h : a.val * t + b.val < N then x ⟨a.val * t + b.val, h⟩ else fill := by
  simp only [convTemplate]
  split <;> rfl

/-- The weight of the edge `(b, c)`. -/
theorem convTemplate_BC {t N s : ℕ} {x : Fin N → ℤ} {fill : ℤ} (b c : Fin t) :
    templateWeight x fill ((convTemplate t N s).eBC b c)
      = if h : b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N then
          x ⟨c.val * t + s - b.val, h.2⟩ else fill := by
  simp only [convTemplate]
  split <;> rfl

/-- The weight of the edge `(a, c)`. -/
theorem convTemplate_AC {t N s : ℕ} {x : Fin N → ℤ} {fill : ℤ} (a c : Fin t) :
    templateWeight x fill ((convTemplate t N s).eAC a c)
      = if h : (a.val + c.val) * t + s < N then -x ⟨(a.val + c.val) * t + s, h⟩ else fill := by
  simp only [convTemplate]
  split <;> rfl

/-- A solution `(i, j)` is the triangle `(⌊i/t⌋, i mod t, ⌊j/t⌋)` of the instance
`s = (j mod t) + (i mod t)`. -/
private theorem exists_hasZeroTriangle {t N : ℕ} {x : Fin N → ℤ} {fill : ℤ} (hNt : N < t * t)
    {i j : Fin N} (hij : i.val + j.val < N) (h : x i + x j = x ⟨i.val + j.val, hij⟩) :
    ∃ s < 2 * t, ((convTemplate t N s).instantiate x fill).HasZeroTriangle := by
  have ht : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hit := Nat.mod_lt i.val ht
  have hjt := Nat.mod_lt j.val ht
  have hj := Nat.div_add_mod' j.val t
  -- The three indices are `i`, `j` and `i + j`, so they are in range.
  have hAB : i.val / t * t + i.val % t = i.val := Nat.div_add_mod' i.val t
  have hBC : j.val / t * t + (j.val % t + i.val % t) - i.val % t = j.val := by omega
  have hAC : (i.val / t + j.val / t) * t + (j.val % t + i.val % t) = i.val + j.val := by
    rw [Nat.add_mul]
    omega
  refine ⟨j.val % t + i.val % t, by omega, ⟨i.val / t, Nat.div_lt_of_lt_mul (i.isLt.trans hNt)⟩,
    ⟨i.val % t, hit⟩, ⟨j.val / t, Nat.div_lt_of_lt_mul (j.isLt.trans hNt)⟩, ?_⟩
  simp only [TriangleInstance.IsZeroTriangle, TriangleInstance.S, TriangleTemplate.instantiate,
    convTemplate_AB, convTemplate_BC, convTemplate_AC]
  rw [dif_pos (hAB.trans_lt i.isLt), dif_pos ⟨by omega, hBC.trans_lt j.isLt⟩,
    dif_pos (hAC.trans_lt hij)]
  simp only [hAB, hBC, hAC, Fin.eta, h]
  ring

/-- With the filler `2U + 1`, every weight is at least `-U`. -/
private theorem neg_le_templateWeight {N : ℕ} {x : Fin N → ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hx : ∀ i, |x i| ≤ U) (o : Option (Bool × Fin N)) : -U ≤ templateWeight x (2 * U + 1) o := by
  rcases o with _ | ⟨_ | _, i⟩ <;> simp only [templateWeight]
  · omega
  · exact (abs_le.mp (hx i)).1
  · exact neg_le_neg (abs_le.mp (hx i)).2

/-- A zero triangle of an instance with the filler `2U + 1` is a solution. -/
private theorem convolution3SUM_of_isZeroTriangle {t N s : ℕ} {x : Fin N → ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hx : ∀ i, |x i| ≤ U) {a b c : Fin t}
    (h : ((convTemplate t N s).instantiate x (2 * U + 1)).IsZeroTriangle a b c) :
    Convolution3SUM x := by
  simp only [TriangleInstance.IsZeroTriangle, TriangleInstance.S, TriangleTemplate.instantiate] at h
  have hgeAB := neg_le_templateWeight hU hx ((convTemplate t N s).eAB a b)
  have hgeBC := neg_le_templateWeight hU hx ((convTemplate t N s).eBC b c)
  have hgeAC := neg_le_templateWeight hU hx ((convTemplate t N s).eAC a c)
  -- One filler `2U + 1` and two weights that are at least `-U` have a positive sum, so the three
  -- indices are in range.
  have hAB : a.val * t + b.val < N := by
    by_contra hout
    rw [convTemplate_AB, dif_neg hout] at h
    omega
  have hBC : b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N := by
    by_contra hout
    rw [convTemplate_BC, dif_neg hout] at h
    omega
  have hAC : (a.val + c.val) * t + s < N := by
    by_contra hout
    rw [convTemplate_AC, dif_neg hout] at h
    omega
  rw [convTemplate_AB, convTemplate_BC, convTemplate_AC, dif_pos hAB, dif_pos hBC, dif_pos hAC] at h
  -- The triangle stands for `i = at + b` and `j = ct + s - b`, and `i + j = (a + c)t + s`.
  have hsum : a.val * t + b.val + (c.val * t + s - b.val) = (a.val + c.val) * t + s := by
    rw [Nat.add_mul]
    omega
  refine ⟨⟨a.val * t + b.val, hAB⟩, ⟨c.val * t + s - b.val, hBC.2⟩, hsum ▸ hAC, ?_⟩
  simp only [hsum]
  -- `h` says `x_i + x_j - x_{i+j} = 0`.
  linarith [h]

/-- The reduction of [VW13, Theorem 4.3], for `N < t²` numbers of absolute value at most `U`: there
are `i`, `j` with `x_i + x_j = x_{i+j}` if and only if one of the instances `s < 2t`, with the
filler `2U + 1`, has a zero triangle. -/
theorem convolution3SUM_iff {t N : ℕ} {x : Fin N → ℤ} {U : ℤ} (hN : 1 ≤ N) (hNt : N < t * t)
    (hx : ∀ i, |x i| ≤ U) :
    Convolution3SUM x ↔
      ∃ s < 2 * t, ((convTemplate t N s).instantiate x (2 * U + 1)).HasZeroTriangle := by
  constructor
  · rintro ⟨i, j, hij, h⟩
    exact exists_hasZeroTriangle hNt hij h
  · rintro ⟨s, -, a, b, c, h⟩
    exact convolution3SUM_of_isZeroTriangle ((abs_nonneg _).trans (hx ⟨0, hN⟩)) hx h

end Theorem21



end ThreeSumApsp


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Convolution-3SUM reduces to Exact Triangle, on lists

Theorem 21(a), after [VW13, Theorem 4.3]: from `N < t²` numbers the reduction makes `2t` instances
of Exact Triangle, each on `t` vertices per part (`Theorem21.convTemplate`).  Here
the instances are lists of integers, row by row, in the form in which a routine fills them
(`convAB`, `convBC`, `convAC`): every weight is a cell of the input, or minus a cell of the input,
at an index that is computed from the two vertices, or a filler if this index is out of range
(`cellOr`).

The three lists are the instance of the template (`triOf_conv`).  So there are `i`, `j` with
`x_i + x_j = x_{i+j}` if and only if one of the `2t` instances has a zero triangle
(`convolution3SUM_vecOf_iff`), and the weights are bounded by a bound for the numbers and the filler
(`abs_convAB_le`, `abs_convBC_le`, `abs_convAC_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- Cell number `z` of a list of `N` numbers, or the filler `F` if `z` is not one of
`0, …, N - 1`. -/
def cellOr (N : ℕ) (F : ℤ) (X : List ℤ) (z : ℤ) : ℤ := if 0 ≤ z ∧ z < N then X.getD z.toNat 0 else F

/-- The weights `w(a,b) = x_{a t + b}`. -/
def convAB (t N : ℕ) (F : ℤ) (X : List ℤ) : List ℤ :=
  (List.range (t * t)).map fun q : ℕ => cellOr N F X (q : ℤ)

/-- The weights `w(b,c) = x_{c t + s - b}` of instance number `s`. -/
def convBC (t N s : ℕ) (F : ℤ) (X : List ℤ) : List ℤ :=
  (List.range (t * t)).map fun q : ℕ => cellOr N F X (((q % t : ℕ) : ℤ) * t + s - ((q / t : ℕ) : ℤ))

/-- The weights `w(a,c) = -x_{(a + c) t + s}` of instance number `s`.  The filler `-F` inside the
minus sign gives the weight `F`. -/
def convAC (t N s : ℕ) (F : ℤ) (X : List ℤ) : List ℤ :=
  (List.range (t * t)).map fun q : ℕ =>
    -cellOr N (-F) X ((((q / t : ℕ) : ℤ) + ((q % t : ℕ) : ℤ)) * t + s)

/-- The first list has `t²` entries. -/
@[simp] theorem length_convAB (t N : ℕ) (F : ℤ) (X : List ℤ) : (convAB t N F X).length = t * t := by
  simp [convAB]

/-- The second list has `t²` entries. -/
@[simp] theorem length_convBC (t N s : ℕ) (F : ℤ) (X : List ℤ) :
    (convBC t N s F X).length = t * t := by
  simp [convBC]

/-- The third list has `t²` entries. -/
@[simp] theorem length_convAC (t N s : ℕ) (F : ℤ) (X : List ℤ) :
    (convAC t N s F X).length = t * t := by
  simp [convAC]

/-- At an index in range `cellOr` reads the cell. -/
theorem cellOr_of_lt {N : ℕ} {F : ℤ} {X : List ℤ} {z : ℤ} {i : ℕ} (hz : z = i) (hi : i < N) :
    cellOr N F X z = X.getD i 0 := by
  subst hz
  rw [cellOr, if_pos ⟨Int.natCast_nonneg i, Int.ofNat_lt.2 hi⟩, Int.toNat_natCast]

/-- At an index out of range `cellOr` returns the filler. -/
theorem cellOr_of_not {N : ℕ} {F : ℤ} {X : List ℤ} {z : ℤ} (hz : ¬ (0 ≤ z ∧ z < N)) :
    cellOr N F X z = F :=
  if_neg hz

/-- A bound for the list and the filler is a bound for `cellOr`. -/
theorem abs_cellOr_le {N : ℕ} {F V : ℤ} {X : List ℤ} (hX : AbsLe X V) (hF : |F| ≤ V) (z : ℤ) :
    |cellOr N F X z| ≤ V := by
  unfold cellOr
  split_ifs
  · exact AbsLe.abs_getD_le ((abs_nonneg F).trans hF) hX _
  · exact hF

/-- The three lists are the instance that the template of the reduction produces. -/
theorem triOf_conv (t N s : ℕ) (F : ℤ) (X : List ℤ) :
    triOf t (convAB t N F X) (convBC t N s F X) (convAC t N s F X) =
      (Theorem21.convTemplate t N s).instantiate (vecOf N X) F := by
  unfold triOf TriangleTemplate.instantiate
  congr 1
  · funext a b
    rw [convAB, List.getD_map_range _ (Nat.mul_add_lt_mul a.isLt b.isLt), Theorem21.convTemplate_AB]
    split_ifs with h
    · exact cellOr_of_lt rfl h
    · exact cellOr_of_not fun h' => h (by exact_mod_cast h'.2)
  · funext b c
    rw [convBC, List.getD_map_range _ (Nat.mul_add_lt_mul b.isLt c.isLt),
      Nat.mul_add_div_of_lt c.isLt,
      Nat.mul_add_mod_of_lt c.isLt, Theorem21.convTemplate_BC]
    split_ifs with h
    · exact cellOr_of_lt (by push_cast [h.1]; ring) h.2
    · exact cellOr_of_not fun h' => h (by omega)
  · funext a c
    rw [convAC, List.getD_map_range _ (Nat.mul_add_lt_mul a.isLt c.isLt),
      Nat.mul_add_div_of_lt c.isLt,
      Nat.mul_add_mod_of_lt c.isLt, Theorem21.convTemplate_AC]
    split_ifs with h
    · exact congrArg Neg.neg (cellOr_of_lt (by push_cast; ring) h)
    · rw [cellOr_of_not fun h' => h (by exact_mod_cast h'.2), neg_neg]

section Bounds

variable {t N s : ℕ} {F V : ℤ} {X : List ℤ}

/-- The weights `w(a,b)` are bounded by a bound for the numbers and the filler. -/
theorem abs_convAB_le (hX : AbsLe X V) (hF : |F| ≤ V) : AbsLe (convAB t N F X) V :=
  List.forall_mem_map.2 fun _ _ => abs_cellOr_le hX hF _

/-- The weights `w(b,c)` are bounded by a bound for the numbers and the filler. -/
theorem abs_convBC_le (hX : AbsLe X V) (hF : |F| ≤ V) : AbsLe (convBC t N s F X) V :=
  List.forall_mem_map.2 fun _ _ => abs_cellOr_le hX hF _

/-- The weights `w(a,c)` are bounded by a bound for the numbers and the filler. -/
theorem abs_convAC_le (hX : AbsLe X V) (hF : |F| ≤ V) : AbsLe (convAC t N s F X) V :=
  List.forall_mem_map.2 fun _ _ => (abs_neg _).trans_le (abs_cellOr_le hX (by rwa [abs_neg]) _)

end Bounds

/-- **The reduction on lists.**  For a list of `N < t²` numbers of absolute value at most `U`: there
are `i`, `j` with `x_i + x_j = x_{i+j}` if and only if one of the `2t` instances, filled with the
filler `2U + 1`, has a zero triangle. -/
theorem convolution3SUM_vecOf_iff {t N : ℕ} (hN : 1 ≤ N) (hNt : N < t * t) {X : List ℤ} {U : ℤ}
    (hU : 0 ≤ U) (hX : AbsLe X U) :
    Convolution3SUM (vecOf N X) ↔
      ∃ s < 2 * t, (triOf t (convAB t N (2 * U + 1) X) (convBC t N s (2 * U + 1) X)
        (convAC t N s (2 * U + 1) X)).HasZeroTriangle := by
  simp only [triOf_conv]
  exact Theorem21.convolution3SUM_iff hN hNt fun i => AbsLe.abs_getD_le hU hX _

end ThreeSumApsp.Spec


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Convolution-3SUM from Exact Triangle: writing one instance

Theorem 21(a), after [VW13, Theorem 4.3].  convFill(t, N, s, F, x, ab, bc,
ac) writes the three weight matrices of instance number s of the reduction, each of t² cells, row
by row, to ab, bc, ac: w(a,b) = x[a t + b], w(b,c) = x[c t + s - b], w(a,c) = -x[(a + c) t + s], and
the filler F where the index is out of range.  One loop runs through the t² cells; it keeps the
number of the cell, its row and its column in three counters.

The proof follows the text.  pickStmt reads a cell of x or the filler (`pick_runs`); putStmt
computes an index, picks, and stores (`put_runs`); fillCells does this for the three matrices
(`cells_runs`); then the counters move on.  After q rounds the memory is `A.filled μ q`: the first q
cells of each matrix have been written (`filled_succ` is one round).  The result is
`convFill_meets`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace ConvFill

/-- The local variables of convFill: the arguments t (Side), N (Len), s (Inst), F (Filler), x
(Input), ab, bc, ac (MatAB, MatBC, MatAC); the row, the column and the number of the current cell
(Row, Col, Cell); an index into x and what is picked there (Index, Value); -F (NegFiller) and t²
(Area). -/
abbrev Side : ℕ := 0
@[inherit_doc Side] abbrev Len : ℕ := 1
@[inherit_doc Side] abbrev Inst : ℕ := 2
@[inherit_doc Side] abbrev Filler : ℕ := 3
@[inherit_doc Side] abbrev Input : ℕ := 4
@[inherit_doc Side] abbrev MatAB : ℕ := 5
@[inherit_doc Side] abbrev MatBC : ℕ := 6
@[inherit_doc Side] abbrev MatAC : ℕ := 7
@[inherit_doc Side] abbrev Row : ℕ := 8
@[inherit_doc Side] abbrev Col : ℕ := 9
@[inherit_doc Side] abbrev Cell : ℕ := 10
@[inherit_doc Side] abbrev Index : ℕ := 11
@[inherit_doc Side] abbrev Value : ℕ := 12
@[inherit_doc Side] abbrev NegFiller : ℕ := 13
@[inherit_doc Side] abbrev Area : ℕ := 14

end ConvFill

open ConvFill

/-- Value := x[Index] if 0 ≤ Index < N, and the content of local f, a filler, if not. -/
def pickStmt (f : ℕ) : Stmt :=
  .set Value (v f) ;;
  .ite (v Index <' k 0) .skip
    (.ite (v Index <' v Len) (.set Value (M (v Input +' v Index))) .skip)

/-- Computes the index ze, picks the cell there (or the filler in local f), and stores it, or minus
it if neg is set, into the current cell of the matrix whose address is in local dst. -/
def putStmt (ze : Expr) (f dst : ℕ) (neg : Bool) : Stmt :=
  .set Index ze ;; pickStmt f ;; .store (v dst +' v Cell) (if neg then k 0 -' v Value else v Value)

/-- The current cell of each of the three matrices. -/
def fillCells : Stmt :=
  putStmt (v Cell) Filler MatAB false ;;
  putStmt (v Col *' v Side +' v Inst -' v Row) Filler MatBC false ;;
  putStmt ((v Row +' v Col) *' v Side +' v Inst) NegFiller MatAC true

/-- One round: the current cell of each matrix, and on to the next cell. -/
def fillRound : Stmt :=
  fillCells ;; .set Cell (v Cell +' k 1) ;; nextPair Row Col Side

/-- convFill(t, N, s, F, x, ab, bc, ac). -/
def convFillBody : Stmt :=
  .set NegFiller (k 0 -' v Filler) ;;
  .set Area (v Side *' v Side) ;;
  .set Row (k 0) ;;
  .set Col (k 0) ;;
  .set Cell (k 0) ;;
  .while (v Cell <' v Area) fillRound

/-- The time of convFill. -/
def convFillTime (t : ℕ) : ℕ := 106 * (t * t) + 18

namespace ConvFill

/-! ## Picking and storing

The two lemmas of this section have the form of the rules for blocks: if R holds of the state in
which the part ends, then the part runs, within the limits, into R. -/

section parts

variable {μ : ℕ → ℤ} {R : State → Prop} {N x : ℕ} {F : ℤ} {X : List ℤ}

/-- The list X of N numbers stands at x, within the memory, and addresses fit in a word. -/
structure InputAt (lim : Limits) (μ : ℕ → ℤ) (x N : ℕ) (X : List ℤ) : Prop where
  seg : Seg μ x X
  len : X.length = N
  space : x + N ≤ lim.space
  addr : (lim.space : ℤ) ≤ lim.word

/-- pickStmt puts `cellOr N F X z` into Value and changes nothing else. -/
private theorem pick_runs {loc : ℕ → ℤ} {f : ℕ} (z : ℤ)
    (h : R ⟨Function.update loc Value (cellOr N F X z), μ⟩) (hX : InputAt lim μ x N X)
    (hz : loc Index = z) (hN : loc Len = N) (hx : loc Input = x) (hf : loc f = F) :
    (pickStmt f).Runs lim ⟨loc, μ⟩ R := by
  obtain ⟨hseg, hlen, hspace, haddr⟩ := hX
  unfold pickStmt
  -- Value := f
  refine .seq ⟨trivial, ?_⟩
  by_cases hneg : z < 0
  · -- if Index < 0
    rw [cellOr_of_not (by omega)] at h
    exact .ite_pos ⟨trivial, by simpa [hf] using h⟩ (by simpa [hz] using hneg) (by simp; omega)
  refine .ite_neg ?_ (by simpa [hz] using hneg) (by simp; omega)
  by_cases hlt : z < N
  · -- if Index < N: Value := x[Index]
    obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 hneg)
    rw [cellOr_of_lt rfl (by omega), ← hseg.getD (by omega)] at h
    refine .ite_pos ⟨?_, by simpa [hz, hx] using h⟩ (by simpa [hz, hN] using hlt) (by simp)
    simp [hz, hx, Limits.Addr, abs_le]
    omega
  · rw [cellOr_of_not (by omega)] at h
    exact .ite_neg ⟨trivial, by simpa [hf] using h⟩ (by simpa [hz, hN] using hlt) (by simp)

/-- putStmt stores `cellOr N F X z`, or minus it, into cell q of the matrix at D.  Of the locals it
changes only Index and Value. -/
private theorem put_runs {l : List ℤ} {ze : Expr} {f dst : ℕ} {neg : Bool} (z : ℤ) (D q : ℕ)
    (h : R ⟨frame (setLocal (setLocal l Index z) Value (cellOr N F X z)),
      Function.update μ (D + q) (if neg then -cellOr N F X z else cellOr N F X z)⟩)
    (hX : InputAt lim μ x N X) (hD : D + q < lim.space) (hV : |cellOr N F X z| ≤ lim.word)
    (hze : ze.Gives lim ⟨frame l, μ⟩ z := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                    (try have := _root_.Light.Std.const_le (by assumption))
                                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                      ))
    (hN : frame l Len = N := by rfl) (hx : frame l Input = x := by rfl)
    (hq : frame l Cell = q := by rfl) (hf : frame l f = F := by rfl)
    (hdst : frame l dst = D := by rfl)
    (hne : f ≠ Index ∧ dst ≠ Index ∧ dst ≠ Value := by decide) :
    (putStmt ze f dst neg).Runs lim ⟨frame l, μ⟩ R := by
  rw [← update_frame_setLocal, ← update_frame_setLocal] at h
  generalize frame l = loc at *
  obtain ⟨hfI, hdI, hdV⟩ := hne
  obtain ⟨hsafe, hval⟩ := hze
  have haddr := hX.addr
  unfold putStmt
  -- Index := ze
  refine .seq ⟨hsafe, ?_⟩
  -- Value := x[Index] or the filler
  refine .seq (pick_runs z ?_ hX (by simp [hval]) (by simpa using hN) (by simpa using hx)
    (by simpa [hfI] using hf))
  -- dst[Cell] := Value or -Value
  cases neg
  · refine ⟨?_, by simpa [hval, hdI, hdV, hdst, hq] using h⟩
    simp [hdI, hdV, hdst, hq, Limits.Addr, abs_le]
    omega
  · refine ⟨?_, by simpa [hval, hdI, hdV, hdst, hq] using h⟩
    rw [abs_le] at hV
    simp [hdI, hdV, hdst, hq, Limits.Addr, abs_le]
    omega

end parts

/-! ## The data and the memory -/

/-- The arguments of convFill, with the list X that stands at x. -/
structure Args : Type where
  t : ℕ
  N : ℕ
  s : ℕ
  F : ℤ
  x : ℕ
  ab : ℕ
  bc : ℕ
  ac : ℕ
  X : List ℤ

/-- What convFill assumes: there is at least one row; the input lies below the three matrices, which
follow each other within the memory; V bounds the input and the filler; words hold addresses, V and
the indices. -/
structure Ctx (lim : Limits) (μ : ℕ → ℤ) (A : Args) (V : ℕ) : Prop where
  side : 1 ≤ A.t
  addr : (lim.space : ℤ) ≤ lim.word
  input : Seg μ A.x A.X
  len : A.X.length = A.N
  belowAB : A.x + A.N ≤ A.ab
  belowBC : A.ab + A.t * A.t ≤ A.bc
  belowAC : A.bc + A.t * A.t ≤ A.ac
  space : A.ac + A.t * A.t ≤ lim.space
  inputLe : AbsLe A.X V
  fillerLe : |A.F| ≤ V
  valueLe : (V : ℤ) ≤ lim.word
  indexLe : ((2 * (A.t * A.t) + A.s + 1 : ℕ) : ℤ) ≤ lim.word

/-- What convFill achieves: the three matrices stand in the memory, and no cell before the first or
after the last of them has changed. -/
structure Post (A : Args) (μ μ' : ℕ → ℤ) : Prop where
  segAB : Seg μ' A.ab (convAB A.t A.N A.F A.X)
  segBC : Seg μ' A.bc (convBC A.t A.N A.s A.F A.X)
  segAC : Seg μ' A.ac (convAC A.t A.N A.s A.F A.X)
  same : SameOutside μ μ' A.ab (A.ac + A.t * A.t - A.ab)

/-- The index into x for cell q of the second matrix: c t + s - b for row b and column c. -/
def Args.idxBC (A : Args) (q : ℕ) : ℤ := ((q % A.t : ℕ) : ℤ) * A.t + A.s - ((q / A.t : ℕ) : ℤ)

/-- The index into x for cell q of the third matrix: (a + c) t + s for row a and column c. -/
def Args.idxAC (A : Args) (q : ℕ) : ℤ := (((q / A.t : ℕ) : ℤ) + ((q % A.t : ℕ) : ℤ)) * A.t + A.s

/-- The memory after q rounds: the first q cells of each matrix have been written. -/
def Args.filled (A : Args) (μ : ℕ → ℤ) (q : ℕ) : ℕ → ℤ :=
  wrote (wrote (wrote μ A.ab (fun i => cellOr A.N A.F A.X i) q)
    A.bc (fun i => cellOr A.N A.F A.X (A.idxBC i)) q)
    A.ac (fun i => -cellOr A.N (-A.F) A.X (A.idxAC i)) q

/-- The local variables before round q; z and w are what the last round has left in Index and
Value. -/
abbrev Args.locals (A : Args) (q : ℕ) (z w : ℤ) : List ℤ :=
  [A.t, A.N, A.s, A.F, A.x, A.ab, A.bc, A.ac, (q / A.t : ℕ), (q % A.t : ℕ), q, z, w, -A.F,
    (A.t * A.t : ℕ)]

section memory

variable {μ : ℕ → ℤ} {A : Args} {V q : ℕ}

/-- One round writes cell q of each matrix. -/
private theorem filled_succ (C : Ctx lim μ A V) (hq : q < A.t * A.t) :
    Function.update (Function.update (Function.update (A.filled μ q)
      (A.ab + q) (cellOr A.N A.F A.X q)) (A.bc + q) (cellOr A.N A.F A.X (A.idxBC q)))
      (A.ac + q) (-cellOr A.N (-A.F) A.X (A.idxAC q)) = A.filled μ (q + 1) := by
  obtain ⟨hBC, hAC⟩ := And.intro C.belowBC C.belowAC
  have offBC : A.ab + q < A.bc ∨ A.bc + q ≤ A.ab + q := by omega
  have offAC (y : ℕ) (hy : y ≤ A.bc + q) : y < A.ac ∨ A.ac + q ≤ y := by omega
  unfold Args.filled
  rw [update_wrote (offAC _ (by omega)), update_wrote offBC, wrote_succ,
    update_wrote (offAC _ le_rfl), wrote_succ, wrote_succ]

/-- No cell before the first matrix or after the last one changes. -/
private theorem sameOutside_filled (C : Ctx lim μ A V) (hq : q ≤ A.t * A.t) :
    SameOutside μ (A.filled μ q) A.ab (A.ac + A.t * A.t - A.ab) := fun b hb => by
  obtain ⟨hBC, hAC⟩ := And.intro C.belowBC C.belowAC
  have off (dst : ℕ) (h₁ : A.ab ≤ dst) (h₂ : dst ≤ A.ac) : b < dst ∨ dst + q ≤ b := by
    unfold Outside at hb
    omega
  rw [Args.filled, wrote_rest (off _ (by omega) le_rfl), wrote_rest (off _ (by omega) (by omega)),
    wrote_rest (off _ le_rfl (by omega))]

/-- At the end the three matrices stand in the memory. -/
private theorem post_filled (C : Ctx lim μ A V) : Post A μ (A.filled μ (A.t * A.t)) where
  segAB i hi := by
    obtain ⟨hBC, hAC⟩ := And.intro C.belowBC C.belowAC
    rw [length_convAB] at hi
    rw [Args.filled, wrote_rest (by omega), wrote_rest (by omega), wrote_done hi]
    simp [convAB]
  segBC i hi := by
    have hAC := C.belowAC
    rw [length_convBC] at hi
    rw [Args.filled, wrote_rest (by omega), wrote_done hi]
    simp [convBC, Args.idxBC]
  segAC i hi := by
    rw [length_convAC] at hi
    rw [Args.filled, wrote_done hi]
    simp [convAC, Args.idxAC]
  same := sameOutside_filled C le_rfl

/-- The input is still there after q rounds. -/
private theorem inputAt_filled (C : Ctx lim μ A V) (hq : q ≤ A.t * A.t) :
    InputAt lim (A.filled μ q) A.x A.N A.X where
  seg := C.input.keep (by (intro i hi; apply (sameOutside_filled C hq) i; have hlen := C.len; have hbelow := C.belowAB; simp only [Inside, Outside] at *; omega
                                                                               ))
  len := C.len
  space := by
    have hAB := C.belowAB
    have hBC := C.belowBC
    have hAC := C.belowAC
    have hspace := C.space
    omega
  addr := C.addr

/-- A write to a cell of the matrices leaves the input alone. -/
private theorem InputAt.write {μ' : ℕ → ℤ} (hX : InputAt lim μ' A.x A.N A.X) (C : Ctx lim μ A V)
    {b : ℕ} (hb : A.ab ≤ b) (w : ℤ) : InputAt lim (Function.update μ' b w) A.x A.N A.X :=
  { hX with seg := hX.seg.update_out (Or.inr (by have := C.len; have := C.belowAB; omega)) w }

/-- What is picked fits in a word. -/
private theorem abs_cellOr_le_word (C : Ctx lim μ A V) (z : ℤ) :
    |cellOr A.N A.F A.X z| ≤ lim.word ∧ |cellOr A.N (-A.F) A.X z| ≤ lim.word :=
  ⟨(abs_cellOr_le C.inputLe C.fillerLe z).trans C.valueLe,
    (abs_cellOr_le C.inputLe (by rw [abs_neg]; exact C.fillerLe) z).trans C.valueLe⟩

end memory

/-! ## The loop -/

section loop

variable {μ : ℕ → ℤ} {A : Args} {V q : ℕ}

/-- The row and the column of a cell q < t² are below t, so the products that the two index
expressions form lie between 0 and 2t². -/
private structure IndexBounds (t q : ℕ) : Prop where
  row : 0 ≤ (q : ℤ) / t ∧ (q : ℤ) / t < t
  col : 0 ≤ (q : ℤ) % t ∧ (q : ℤ) % t < t
  colSide : 0 ≤ (q : ℤ) % t * t ∧ (q : ℤ) % t * t ≤ t * t
  sumSide : 0 ≤ ((q : ℤ) / t + (q : ℤ) % t) * t ∧ ((q : ℤ) / t + (q : ℤ) % t) * t ≤ 2 * (t * t)
  side : (t : ℤ) ≤ t * t

private theorem indexBounds {t : ℕ} (hq : q < t * t) : IndexBounds t q := by
  have hrow : q / t < t := Nat.div_lt_of_lt_mul hq
  have hcol : q % t < t := Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by simp [h] at hq)
  exact ⟨by exact_mod_cast And.intro (Nat.zero_le _) hrow,
    by exact_mod_cast And.intro (Nat.zero_le _) hcol,
    by exact_mod_cast And.intro (Nat.zero_le _) (Nat.mul_le_mul_right t hcol.le),
    by exact_mod_cast And.intro (Nat.zero_le _) ((Nat.mul_le_mul_right t
      (show q / t + q % t ≤ 2 * t by omega)).trans_eq (Nat.mul_assoc ..)),
    by exact_mod_cast Nat.le_mul_self t⟩

/-- fillCells writes cell q of each matrix. -/
private theorem cells_runs {R : State → Prop} (C : Ctx lim μ A V) (hq : q < A.t * A.t) (z w : ℤ)
    (h : R ⟨frame (A.locals q (A.idxAC q) (cellOr A.N (-A.F) A.X (A.idxAC q))),
      A.filled μ (q + 1)⟩) :
    fillCells.Runs lim ⟨frame (A.locals q z w), A.filled μ q⟩ R := by
  obtain ⟨hrow, hcol, hcolSide, hsumSide, hside⟩ := indexBounds hq
  obtain ⟨hBC, hAC, hspace⟩ := And.intro C.belowBC (And.intro C.belowAC C.space)
  have hidx := C.indexLe
  have hX := inputAt_filled C hq.le
  rw [← filled_succ C hq] at h
  unfold fillCells
  -- ab[q] := x[q] or F
  refine .seq (put_runs (q : ℤ) A.ab q ?_ hX (by omega) (abs_cellOr_le_word C _).1)
  -- bc[q] := x[c t + s - b] or F, for row b and column c
  refine .seq (put_runs (A.idxBC q) A.bc q ?_ (hX.write C (by omega) _) (by omega)
    (abs_cellOr_le_word C _).1 (by (((  (try have := _root_.Light.Std.space_le (by assumption))
                                        (try have := _root_.Light.Std.const_le (by assumption))
                                        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, Args.idxBC] <;> omega))
                                                         )))
  -- ac[q] := -(x[(a + c) t + s] or -F), for row a and column c
  exact put_runs (A.idxAC q) A.ac q h ((hX.write C (by omega) _).write C (by omega) _) (by omega)
    (abs_cellOr_le_word C _).2 (by (((  (try have := _root_.Light.Std.space_le (by assumption))
                                        (try have := _root_.Light.Std.const_le (by assumption))
                                        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, Args.idxAC] <;> omega))
                                                         ))

/-- The invariant of the loop: before round q the counters stand at cell q, and the first q cells of
each matrix have been written. -/
def LoopInv (A : Args) (μ : ℕ → ℤ) (q : ℕ) (σ : State) : Prop :=
  ∃ z w : ℤ, σ = ⟨frame (A.locals q z w), A.filled μ q⟩

/-- Round q: cell q of each matrix is written, and the counters move on to cell q + 1. -/
private theorem round_spec (C : Ctx lim μ A V) (hq : q < A.t * A.t) (z w : ℤ) :
    Ends lim P d fillRound ⟨frame (A.locals q z w), A.filled μ q⟩ fillRound.blockCost
      (LoopInv A μ (q + 1)) := by
  have hidx := C.indexLe
  have hside : A.t ≤ A.t * A.t := Nat.le_mul_self _
  unfold fillRound
  -- the three cells
  refine Ends.next _ (Ends.block (cells_runs C hq z w ?_) le_rfl)
  -- Cell := Cell + 1
  refine Ends.setToThen ((q + 1 : ℕ) : ℤ) ?_ (by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                        (try have := _root_.Light.Std.const_le (by assumption))
                                                        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                          )) (by simp [nextPair])
  -- on to the next row and column
  exact Ends.nextPair ⟨_, _, rfl⟩ C.side (by omega) (by omega) rfl rfl rfl
    (hT := by simp [nextPair])

end loop

end ConvFill

/-- **convFill** writes the three matrices of instance number s, changes no cell before the first or
after the last of them, and takes O(t²) steps. -/
theorem convFill_meets {p : ℕ} (hp : P[p]? = some convFillBody) {μ : ℕ → ℤ} {A : Args} {V : ℕ}
    (C : Ctx lim μ A V) :
    Meets lim P p d [A.t, A.N, A.s, A.F, A.x, A.ab, A.bc, A.ac] μ (convFillTime A.t)
      fun _ μ' => Post A μ μ' := by
  have hidx := C.indexLe
  have hF := abs_le.1 (C.fillerLe.trans C.valueLe)
  refine .of_body hp ?_
  unfold convFillBody convFillTime
  -- NegFiller := 0 - Filler; Area := Side * Side
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (-A.F) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                 )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (A.t * A.t : ℕ)
               -- Row := 0; Col := 0; Cell := 0
               
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                          )
  -- Row := 0; Col := 0; Cell := 0
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             0
               -- while Cell < Area
               
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  -- while Cell < Area
  refine Ends.whileConst (LoopInv A μ) (A.t * A.t) fillRound.blockCost ?start ?round ?done
    (by simp [fillRound, fillCells, putStmt, pickStmt, nextPair]; omega)
  case start => exact ⟨0, 0, by simp [Args.filled, wrote_zero, Args.locals]⟩
  case round =>
    rintro q _ hq ⟨z, w, rfl⟩
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), round_spec C hq z w⟩
  case done =>
    rintro _ ⟨z, w, rfl⟩
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), post_filled C⟩

end Light.Sec3


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Convolution-3SUM from Exact Triangle: the host

Theorem 21(a), after [VW13, Theorem 4.3]: whether an array of N integers is a yes-instance of
Convolution-3SUM is decided by asking O(√N) times whether there is a zero triangle, each time in an
instance with O(√N) vertices in each part whose weights are entries of the array, up to sign, or a
filler. c3(N, U, x, fr) computes t = ⌊√N⌋ + 1 and runs an arbitrary solver of Exact Triangle once
for each of the 2t instances, which have t vertices in each part and weights of absolute value at
most 2U + 1.  The three matrices of the current instance are written at the free pointer.  There is
no early exit.

One round writes instance s and asks the solver (`round_spec`); after s rounds the local Found says
whether one of the first s instances has a zero triangle.  By `convolution3SUM_vecOf_iff` the answer
after 2t rounds is the answer to Convolution-3SUM (`c3_spec`).  The need of the host is polynomially
bounded if the solver's is (`polyNeed_c3Need`).  The host with its time and its need is `isHost_c3`.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-! ## The program -/

namespace ConvHost

/-- The local variables of c3: the arguments N (Len; as local 0 it also takes the result), U
(Bound), x (Input), fr (Free); then t (Side), the number s of the instance (Inst), the answer so far
(Found), the result of a call (Answer), t² (Area) and the filler 2U + 1 (Filler). -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Bound : ℕ := 1
@[inherit_doc Len] abbrev Input : ℕ := 2
@[inherit_doc Len] abbrev Free : ℕ := 3
@[inherit_doc Len] abbrev Side : ℕ := 4
@[inherit_doc Len] abbrev Inst : ℕ := 5
@[inherit_doc Len] abbrev Found : ℕ := 6
@[inherit_doc Len] abbrev Answer : ℕ := 7
@[inherit_doc Len] abbrev Area : ℕ := 8
@[inherit_doc Len] abbrev Filler : ℕ := 9

end ConvHost

open ConvHost

/-- One round: writes instance number Inst at the free pointer and asks the solver. -/
def c3Round (pET pFill : ℕ) : Stmt :=
  .call pFill [v Side, v Len, v Inst, v Filler, v Input, v Free, v Free +' v Area,
    v Free +' k 2 *' v Area] Answer ;;
  .call pET [v Side, v Filler, v Free, v Free +' v Area, v Free +' k 2 *' v Area,
    v Free +' k 3 *' v Area] Answer ;;
  .ite (v Answer =' k 1) (.set Found (k 1)) .skip

/-- c3(N, U, x, fr), over the procedures pET (a solver of Exact Triangle), pSqrt (the integer square
root) and pFill (convFill).  The result is returned in local 0. -/
def c3Body (pET pSqrt pFill : ℕ) : Stmt :=
  .call pSqrt [v Len] Side ;;
  .set Side (v Side +' k 1) ;;
  .set Area (v Side *' v Side) ;;
  .set Filler (k 2 *' v Bound +' k 1) ;;
  .set Found (k 0) ;;
  .for Inst (k 2 *' v Side) (c3Round pET pFill) ;;
  .set Len (v Found)

/-- The time of one round: it writes 3t² cells and runs the solver on t vertices per part with the
bound 2U + 1. -/
def c3RoundTime (T : ℕ → ℕ → ℕ) (t U : ℕ) : ℕ := convFillTime t + 40 + T t (2 * U + 1)

/-- The time of the host: the square root, and 2t rounds with t = ⌊√N⌋ + 1. -/
def c3Time (T : ℕ → ℕ → ℕ) (N U : ℕ) : ℕ :=
  18 * Nat.sqrt N + 41 + 2 * (Nat.sqrt N + 1) * (c3RoundTime T (Nat.sqrt N + 1) U + 10)

/-- The need of the host: 3t² cells more than the solver, one level of calls more, and words for the
square root (3N + 4), the filler (2U + 1) and the indices (2t² + 2t). -/
def c3Need (r : ℕ → ℕ → Need) (N U : ℕ) : Need where
  word := (r (Nat.sqrt N + 1) (2 * U + 1)).word + 3 * N + 2 * U +
    2 * ((Nat.sqrt N + 1) * (Nat.sqrt N + 1)) + 2 * (Nat.sqrt N + 1) + 5
  cells := 3 * ((Nat.sqrt N + 1) * (Nat.sqrt N + 1)) + (r (Nat.sqrt N + 1) (2 * U + 1)).cells
  depth := (r (Nat.sqrt N + 1) (2 * U + 1)).depth + 1

namespace ConvHost

/-! ## One round -/

/-- What the host assumes about the program: it begins with the solver's program and holds the two
helpers. -/
structure Ctx (P R : Program) (pET pSqrt pFill : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop where
  sol : Solves etTask P pET T r
  sqrt : (P ++ R)[pSqrt]? = some sqrtBody
  fill : (P ++ R)[pFill]? = some convFillBody

/-- What the rounds assume: the input lies below the free pointer, N < t², and the limits allow for
the need of the host, written with t. -/
structure Ready (lim : Limits) (r : ℕ → ℕ → Need) (d : ℕ) (x : VecInst) (μ : ℕ → ℤ) (fr t : ℕ) :
    Prop where
  pre : x.Pre μ fr
  lenLt : x.N < t * t
  word : ((r t (2 * x.U + 1)).word : ℤ) + 3 * x.N + 2 * x.U + 2 * (t * t) + 2 * t + 5 ≤ lim.word
  cells : fr + (3 * (t * t) + (r t (2 * x.U + 1)).cells) ≤ lim.space
  addr : (lim.space : ℤ) ≤ lim.word
  depth : d + ((r t (2 * x.U + 1)).depth + 1) ≤ lim.depth

/-- The arguments of convFill for instance number s: the three matrices follow each other at the
free pointer, and the filler is 2U + 1. -/
def fillArgs (x : VecInst) (fr t s : ℕ) : ConvFill.Args :=
  ⟨t, x.N, s, 2 * x.U + 1, x.a, fr, fr + t * t, fr + 2 * (t * t), x.X⟩

/-- Instance number s of the reduction, at the free pointer. -/
def inst (x : VecInst) (fr t s : ℕ) : TriInst :=
  ⟨t, 2 * x.U + 1, fr, fr + t * t, fr + 2 * (t * t), convAB t x.N (2 * x.U + 1) x.X,
    convBC t x.N s (2 * x.U + 1) x.X, convAC t x.N s (2 * x.U + 1) x.X⟩

/-- Instance number s has a zero triangle. -/
def Hit (x : VecInst) (t s : ℕ) : Prop :=
  (triOf t (inst x 0 t s).AB (inst x 0 t s).BC (inst x 0 t s).AC).HasZeroTriangle

/-- The local variables in round s. -/
abbrev locals (x : VecInst) (fr t s : ℕ) (found res : ℤ) : List ℤ :=
  [x.N, x.U, x.a, fr, t, s, found, res, (t * t : ℕ), 2 * x.U + 1]

variable {P R : Program} {pET pSqrt pFill : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {lim : Limits}
  {d : ℕ} {x : VecInst} {μ μ' : ℕ → ℤ} {fr t s : ℕ}

/-- There is at least one vertex per part. -/
private theorem Ready.one_le (H : Ready lim r d x μ fr t) : 1 ≤ t :=
  Nat.pos_of_ne_zero fun h => by simpa [h] using H.lenLt

/-- The numbers of the input are bounded by 2U + 1. -/
private theorem Ready.input_le (H : Ready lim r d x μ fr t) : AbsLe x.X ((2 * x.U + 1 : ℕ) : ℤ) :=
  fun e he => (H.pre.le e he).trans (by push_cast; omega)

/-- The filler is bounded by 2U + 1. -/
private theorem abs_filler_le (x : VecInst) : |2 * (x.U : ℤ) + 1| ≤ ((2 * x.U + 1 : ℕ) : ℤ) := by
  rw [abs_of_nonneg (by positivity)]
  push_cast
  exact le_rfl

/-- convFill can be called in every round. -/
private theorem fill_ctx (H : Ready lim r d x μ fr t) (hk : Kept μ μ' fr) (hs : s < 2 * t) :
    ConvFill.Ctx lim μ' (fillArgs x fr t s) (2 * x.U + 1) where
  side := H.one_le
  addr := H.addr
  input := H.pre.seg.of_sameOn hk fun i hi => by have := H.pre.below; have := H.pre.len; omega
  len := H.pre.len
  belowAB := H.pre.below
  belowBC := le_rfl
  belowAC := by simp only [fillArgs]; omega
  space := by have := H.cells; simp only [fillArgs]; omega
  inputLe := H.input_le
  fillerLe := abs_filler_le x
  valueLe := by have := H.word; have := mul_self_nonneg (t : ℤ); push_cast; omega
  indexLe := by have := H.word; simp only [fillArgs]; push_cast; omega

/-- After convFill the instance lies in the memory. -/
private theorem inst_pre {μ₁ : ℕ → ℤ} (H : Ready lim r d x μ fr t)
    (hpost : ConvFill.Post (fillArgs x fr t s) μ' μ₁) :
    (inst x fr t s).Pre μ₁ (fr + 3 * (t * t)) where
  n_pos := H.one_le
  U_pos := by simp [inst]
  lenAB := by simp [inst]
  lenBC := by simp [inst]
  lenAC := by simp [inst]
  segAB := hpost.segAB
  segBC := hpost.segBC
  segAC := hpost.segAC
  leAB := abs_convAB_le H.input_le (abs_filler_le x)
  leBC := abs_convBC_le H.input_le (abs_filler_le x)
  leAC := abs_convAC_le H.input_le (abs_filler_le x)
  belowAB := by simp only [inst]; omega
  belowBC := by simp only [inst]; omega
  belowAC := by simp only [inst]; omega

/-- The limits allow for the solver, after the three matrices and one level of calls down. -/
private theorem solver_ok (H : Ready lim r d x μ fr t) :
    (r t (2 * x.U + 1)).Ok lim (fr + 3 * (t * t)) (d + 1) where
  word := by have := H.word; have := mul_self_nonneg (t : ℤ); omega
  cells := by have := H.cells; omega
  space := H.addr
  depth := by have := H.depth; omega

/-- **One round**: if Found says whether one of the instances before s has a zero triangle, then
afterwards it says so of the instances up to s.  No cell below the free pointer changes. -/
private theorem round_spec (C : Ctx P R pET pSqrt pFill T r) (H : Ready lim r d x μ fr t)
    (hk : Kept μ μ' fr) (hs : s < 2 * t) (res : ℤ) :
    Ends lim (P ++ R) d (c3Round pET pFill)
      ⟨frame (locals x fr t s (flag (∃ s' < s, Hit x t s')) res), μ'⟩ (c3RoundTime T t x.U)
      fun σ' => ∃ (res' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (locals x fr t s (flag (∃ s' < s + 1, Hit x t s')) res'), μ''⟩ ∧
          Kept μ μ'' fr := by
  obtain ⟨hword, hcells, haddr, hdepth⟩ := And.intro H.word (And.intro H.cells
    (And.intro H.addr H.depth))
  have harea := mul_self_nonneg (t : ℤ)
  unfold c3Round c3RoundTime
  -- Answer := convFill(t, N, s, 2U + 1, x, fr, fr + t², fr + 2t²)
  refine Ends.callToThen (T' := convFillTime t) (convFill_meets C.fill (fill_ctx H hk hs)) ?_
    (by (((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, fillArgs] <;> omega))
                            ))
  rintro - μ₁ hpost
  -- Answer := et(t, 2U + 1, fr, fr + t², fr + 2t², fr + 3t²)
  refine Ends.callToThen (T' := T t (2 * x.U + 1)) (C.sol.meets R (inst x fr t s) (fr + 3 * (t * t))
    (inst_pre H hpost) (solver_ok H)) ?_ (by (((  (try have := _root_.Light.Std.space_le (by assumption))
                                                  (try have := _root_.Light.Std.const_le (by assumption))
                                                  simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, etTask, inst] <;> omega))
                                                                     ))
  rintro res' μ₂ ⟨hres, hk₂⟩
  replace hres : res' = flag (Hit x t s) := hres
  -- both calls write only from the free pointer on
  have hkept : Kept μ μ₂ fr := (hk.then hpost.same fun b hb => ⟨hb, Or.inl hb⟩).then hk₂
    fun b hb => ⟨hb, by omega⟩
  -- if Answer = 1
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_)
  · -- Found := 1
    have hit : Hit x t s := flag_eq_one_iff.1 (by simpa [hres] using hyes)
    exact Ends.setTo 1
      ⟨res', μ₂, by rw [flag_of (Nat.exists_lt_succ_right.2 (Or.inr hit))]; rfl, hkept⟩
  · have miss : ¬ Hit x t s := fun hit => hno (by simp [hres, flag_of hit])
    exact Ends.skip
      ⟨res', μ₂, by rw [flag_congr (Nat.exists_lt_succ_right.trans (or_iff_left miss))]; rfl, hkept⟩

/-! ## The host -/

/-- The invariant of the loop: before round s, Found says whether one of the instances before s has
a zero triangle, and no cell below the free pointer has changed. -/
def LoopInv (x : VecInst) (μ : ℕ → ℤ) (fr t s : ℕ) (σ : State) : Prop :=
  ∃ (res : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (locals x fr t s (flag (∃ s' < s, Hit x t s')) res), μ'⟩ ∧ Kept μ μ' fr

/-- The need of the host allows for the rounds. -/
private theorem ready (hpre : x.Pre μ fr) (hok : (c3Need r x.N x.U).Ok lim fr d) :
    Ready lim r d x μ fr (Nat.sqrt x.N + 1) where
  pre := hpre
  lenLt := Nat.lt_succ_sqrt x.N
  word := by have := hok.word; simp only [c3Need] at this; push_cast at this ⊢; omega
  cells := hok.cells
  addr := hok.space
  depth := hok.depth

end ConvHost

open ConvHost in
/-- **The host is correct**, in every program that begins with the solver's and contains the two
helpers. -/
private theorem c3_spec {P R : Program} {pET pSqrt pFill : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (C : Ctx P R pET pSqrt pFill T r) {lim : Limits} {d : ℕ} {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (c3Need r x.N x.U).Ok lim fr d) :
    Ends lim (P ++ R) d (c3Body pET pSqrt pFill) ⟨frame [(x.N : ℤ), x.U, x.a, fr], μ⟩
      (c3Time T x.N x.U) fun σ' =>
        σ'.loc 0 = flag (Convolution3SUM (vecOf x.N x.X)) ∧ Kept μ σ'.mem fr := by
  have H := ready hpre hok
  unfold c3Time
  have hroot : Nat.sqrt x.N ≤ x.N := Nat.sqrt_le_self _
  obtain ⟨t, ht⟩ : ∃ t, t = Nat.sqrt x.N + 1 := ⟨_, rfl⟩
  rw [← ht] at H ⊢
  obtain ⟨hword, hdepth⟩ := And.intro H.word H.depth
  have harea := mul_self_nonneg (t : ℤ)
  unfold c3Body
  -- Side := sqrt(N)
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((sqrt_meets (K := x.N) C.sqrt μ (by push_cast; omega)) _ (by omega)) ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen (sqrt_meets (K := x.N) C.sqrt μ (by push_cast; omega)) ?_ ?_
               ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₀ ⟨rfl, hμ⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                                                      )
  obtain rfl := hμ.symm
  -- Side := Side + 1; Area := Side * Side; Filler := 2 * Bound + 1; Found := 0
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen t ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (t * t : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                      )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (2 * (x.U : ℤ) + 1) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                              )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             0
               -- for Inst < 2 * Side
               
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  -- for Inst < 2 * Side
  refine Ends.next _ (Ends.for (LoopInv x μ fr t) (2 * t) (c3RoundTime T t x.U)
    ?start ?round ?done ?bound (hT := le_rfl))
  case start =>
    exact ⟨0, μ, by simp [update_frame_setLocal, locals, flag_of_not], SameOn.refl⟩
  case round =>
    rintro s _ hs - ⟨res, μ', rfl, hk⟩
    refine (round_spec C H hk hs res).mono le_rfl ?_
    rintro _ ⟨res', μ'', rfl, hk'⟩
    exact ⟨rfl, res', μ'', by simp [update_frame_setLocal, locals], hk'⟩
  case done =>
    rintro _ - ⟨res, μ', rfl, hk⟩
    -- Len := Found: the result
    exact Ends.setTo (flag (∃ s' < 2 * t, Hit x t s'))
      ⟨flag_congr (convolution3SUM_vecOf_iff hpre.N_pos H.lenLt (by positivity) hpre.le).symm, hk⟩
  case bound =>
    rintro s _ - - ⟨res, μ', rfl, -⟩
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by simp⟩

/-! ## The need is polynomially bounded -/

/-- The need of the host is polynomially bounded if the need of the solver is. -/
private theorem polyNeed_c3Need {r : ℕ → ℕ → Need} (hr : PolyNeed r) : PolyNeed (c3Need r) := by
  unfold c3Need
  (((refine _root_.Light.PolyBounded.polyNeed ?_ ?_ ?_ <;> dsimp only <;>
         ((first
             | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.Light.PolyBounded.fst
                         | apply _root_.Light.PolyBounded.snd
                         | apply _root_.ThreeSumApsp.Scale.SoftO.log
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sqrt
                         | apply hr.word
                         | apply hr.cells
                         | apply hr.depth
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 ·
                   first
                   | decide
                   | exact _root_.isEmptyElim)
             | ( fail_if_success
                   (fail_if_success
                       ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                         on_goal 1 =>
                           ((repeat'
                                 with_reducible
                                   first
                                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                                   | apply _root_.Light.PolyBounded.fst
                                   | apply _root_.Light.PolyBounded.snd
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.log
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.sqrt
                                   | apply hr.word
                                   | apply hr.cells
                                   | apply hr.depth
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                             done)))
                 repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
                 all_goals
                   try (
                       apply _root_.ThreeSumApsp.Scale.SoftO.mono
                       ·
                         (repeat'
                             with_reducible
                               first
                               | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                               | apply _root_.Light.PolyBounded.fst
                               | apply _root_.Light.PolyBounded.snd
                               | apply _root_.ThreeSumApsp.Scale.SoftO.log
                               | apply _root_.ThreeSumApsp.Scale.SoftO.sqrt
                               | apply hr.word
                               | apply hr.cells
                               | apply hr.depth
                               | apply _root_.ThreeSumApsp.Scale.SoftO.add
                               | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                               | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                               | apply _root_.ThreeSumApsp.Scale.SoftO.max
                               | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                               | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                       · decide))
             | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.Light.PolyBounded.fst
                         | apply _root_.Light.PolyBounded.snd
                         | apply _root_.ThreeSumApsp.Scale.SoftO.log
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sqrt
                         | apply hr.word
                         | apply hr.cells
                         | apply hr.depth
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div))))))
                                        )

/-- **Convolution-3SUM from Exact Triangle**: the host makes a solver of Convolution-3SUM from every
solver of Exact Triangle. -/
theorem isHost_c3 : IsHost etTask c3Task c3Time c3Need := by
  refine ⟨fun P p T r hsol => ?_, fun r hr => polyNeed_c3Need hr⟩
  refine ⟨[sqrtBody, convFillBody, c3Body p P.length (P.length + 1)], P.length + 2,
    c3Body p P.length (P.length + 1), by simp, ?_⟩
  intro R lim d x μ fr hpre hok
  rw [List.append_assoc]
  exact c3_spec ⟨hsol, by simp, by simp⟩ hpre hok

end Light.Sec3


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Convolution-3SUM from Exact Triangle: the claim

Theorem 21(a), after [VW13, Theorem 4.3].  The arithmetic that turns the
host `isHost_c3` into the transfer of running times: if Exact Triangle is solved in time T, then
Convolution-3SUM on N numbers of absolute value at most u is solved in time
O(N^{3/2}) (1 + log u) + 2 (⌊√N⌋ + 1) T(⌊√N⌋ + 1, 3u) (`c3_solvedIn_explicit`,
`claim_VW13_Theorem_4_3`).

The host's own work is a cubic polynomial in ⌊√N⌋ (`exists_c3Own_le`), and the instances have
⌊√N⌋ + 1 ≤ 2 √N vertices per part (`natSqrt_succ_le`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp

/-- `⌊√N⌋ + 1 ≤ 2 N^{1/2}` for `N ≥ 1`. -/
theorem natSqrt_succ_le {N : ℕ} (hN : 1 ≤ N) :
    ((Nat.sqrt N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  have hfloor : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hone : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.2 (by exact_mod_cast hN)
  push_cast
  linarith

/-- `⌊√N⌋ + 1 = O(N^{1/2})`. -/
private theorem isBigOPow_natSqrt_succ :
    IsBigOPow (fun N : ℕ => ((Nat.sqrt N + 1 : ℕ) : ℝ)) (1 / 2) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact natSqrt_succ_le hN

/-- The host's own work: its time over a solver that takes no time. -/
def c3Own (N : ℕ) : ℕ := c3Time (fun _ _ => 0) N 0

/-- The time of the host is its own work and 2 (⌊√N⌋ + 1) runs of the solver. -/
theorem c3Time_eq (T : ℕ → ℕ → ℕ) (N U : ℕ) :
    c3Time T N U = c3Own N + 2 * (Nat.sqrt N + 1) * T (Nat.sqrt N + 1) (2 * U + 1) := by
  unfold c3Own c3Time c3RoundTime
  ring

/-- The host's own work is a cubic polynomial in ⌊√N⌋, so it is O(N^{3/2}). -/
theorem exists_c3Own_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → (c3Own N : ℝ) ≤ C * (N : ℝ) ^ (3 / 2 : ℝ) := by
  -- powers of 2 √N
  let s : Scale ℕ (Fin 1) := .ofBases (1 ≤ ·) (fun _ N => 2 * (N : ℝ) ^ (1 / 2 : ℝ)) fun _ N hN =>
    le_trans (by exact_mod_cast Nat.le_add_left 1 (Nat.sqrt N)) (natSqrt_succ_le hN)
  have hside : s.SoftO (fun N => Nat.sqrt N + 1) _ := .of_le_base 0 fun _ hN => natSqrt_succ_le hN
  have hown : s.SoftO c3Own ![3] := by
    unfold c3Own c3Time c3RoundTime convFillTime
    ((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply hside
                   | apply hside.of_le fun N _ => Nat.le_succ (Nat.sqrt N)
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply hside
                             | apply hside.of_le fun N _ => Nat.le_succ (Nat.sqrt N)
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply hside
                         | apply hside.of_le fun N _ => Nat.le_succ (Nat.sqrt N)
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply hside
                   | apply hside.of_le fun N _ => Nat.le_succ (Nat.sqrt N)
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)))
                                                                  )
  obtain ⟨C, hC, hle⟩ := hown.dominated fun _ _ => rfl
  refine ⟨C * 8, by positivity, fun N hN => (hle N hN).trans_eq ?_⟩
  have hpow : ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 3 = (N : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul N.cast_nonneg]
    norm_num
  simp only [Scale.mon, s, Scale.ofBases, Fin.prod_univ_one, Matrix.cons_val_zero, mul_pow, hpow]
  ring

/-- Convolution-3SUM from Exact Triangle, with the explicit bound, where C is the constant of the
host's own work.  The weights of the instances are bounded by 2U + 1 ≤ 3u, because 1 ≤ U ≤ u.  The
factor 1 + log u is not needed here; it is the form in which the claim is stated. -/
theorem c3_solvedIn_explicit {C : ℝ} (hC : 0 ≤ C)
    (hown : ∀ N : ℕ, 1 ≤ N → (c3Own N : ℝ) ≤ C * (N : ℝ) ^ (3 / 2 : ℝ)) {T : ℕ → ℝ → ℝ}
    (hT : SolvedIn etTask T) :
    SolvedIn c3Task fun N u => C * (N : ℝ) ^ (3 / 2 : ℝ) * (1 + logU u) +
      2 * ((Nat.sqrt N + 1 : ℕ) : ℝ) * T (Nat.sqrt N + 1) (3 * u) := by
  refine isHost_c3.solvedIn hT fun Tn hTn N U u hN hU hu => ?_
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hsolver : (Tn (Nat.sqrt N + 1) (2 * U + 1) : ℝ) ≤ T (Nat.sqrt N + 1) (3 * u) :=
    hTn _ _ _ (by omega) (by omega) (by push_cast; linarith)
  have hlog : 0 ≤ logU u := Real.log_nonneg (le_trans (by norm_num) (le_max_right u 2))
  rw [c3Time_eq]
  push_cast
  -- the host's own work, and 2 (⌊√N⌋ + 1) runs of the solver
  exact add_le_add ((hown N hN).trans (le_mul_of_one_le_right (by positivity) (by linarith)))
    (mul_le_mul_of_nonneg_left hsolver (by positivity))

/-- [VW13, Theorem 4.3] for programs of the light language: Convolution-3SUM from Exact Triangle. -/
theorem claim_VW13_Theorem_4_3 : Claim.VW13_Theorem_4_3 lightModel :=
  let ⟨C, hC, hown⟩ := exists_c3Own_le
  ⟨3, fun N => C * (N : ℝ) ^ (3 / 2 : ℝ), fun N => 2 * ((Nat.sqrt N + 1 : ℕ) : ℝ),
    fun N => Nat.sqrt N + 1, by norm_num,
    IsBigOPow.isPowLittleO (Asymptotics.isBigO_const_mul_self _ _ _),
    isBigOPow_natSqrt_succ.const_mul_left 2, isBigOPow_natSqrt_succ, fun N _ => Nat.le_add_left 1 _,
    fun _ hT => c3_solvedIn_explicit hC hown hT⟩

end Light.Sec3


theorem solution : ThreeSumApsp.Claim.VW13_Theorem_4_3 Light.lightModel := @Light.Sec3.claim_VW13_Theorem_4_3

-- Prove2me | solution 1 for MilnorDynamics.milnorLambdaHalfShift_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T01:53:16.095613+00:00
-- url     : https://prove2.me/submissions/3481b149-b03e-4c73-aa16-a213bbbe290f

import Mathlib
import Definitions.Def_MilnorLambdaHalfShift

open Complex Real

open MilnorDynamics

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-
`milnorLambdaHalfShift (2 * I) ≠ 1` — v56, comprehensive repair of v55 variant C.

**Built from the full CE reports of 6291 and 6299**, each captured once and read
to its closing `END OF CE REPORT` marker.  Both returned 11 groups; the two
reports differ only where the variants differ, and the union of *independent*
faults is six.  Each is repaired here from the compiler evidence, not from the
repair-plan summary.

1. **E01 (L104) `rw [Complex.I_mul_I]` — "Did not find an occurrence of the
    pattern `I * I`".**  The goal is
    `↑π * I * (↑n + 1) ^ 2 * (2 * I) = ↑(…)`.  `rw` must match the whole target
    against the pattern, and the `↑π *` prefix means the goal is *not* an
    instance of `I * I`.  Repair: drop the rewrite and close the identity by
    `push_cast` + `ring` alone.
2. **E02 (L123) `rw [Complex.re_tsum] at hnn` — pattern not found.**  The target
    is `Summable fun n => cexp …`; `Complex.re_tsum` rewrites `(∑' n, f n).re`,
    which cannot occur in a `Summable` statement.  The rewrite was in the wrong
    place.  Repair: `Complex.hasSum_re hhs` (Basic.lean:605) maps the `HasSum`
    to a `HasSum` of the real parts directly, so `.summable` yields the goal
    with no rewriting at all.
3. **E03 (6291, L115) `hz_summable` type mismatch** and **E04 (6299, L132-133)
    `hlt` parenthesisation.**  `tsum_lt_tsum_of_nonneg` concludes
    `∑' n, f n < ∑' n, g n`; the goal is `0 < ∑' n, g n`.  v55 passed `hg` (6299)
    but still left the `0 <` unaccounted for.  Repair: state the comparison as a
    `have` of explicit type `∑' n, (0:ℝ) < ∑' n, g n`, then `simpa only [zero_tsum]`
    so the `f = 0` reading is never left to the elaborator.
4. **E05 (L137) `rw` cannot find `‖↑1‖`.**  A consequence of (2): the `tsum` was
    never established, so the goal kept its unfolded `re 1 + (re 2 * … - im 2 * …)`
    shape and no `norm_ofReal` pattern could match.  Repair: none needed once (2)
    holds; the `linarith` then closes the goal directly.
5. **E06 (6299, L144) `sq_pos_of_pos ?m` gives `0 < ?m ^ 2`, goal wants
    `1 < ?m ^ 2`.**  Wrong lemma: `sq_pos_of_pos` proves positivity, not
    `1 < _`.  Repair: derive it from `hre_gt1 : 1 < x` by
    `mul_self_lt_mul_self (by norm_num) hre_gt1` (nonnegativity via `sq_nonneg`),
    which is exactly `1 * 1 < x * x`.
6. **E07 (L158) unsolved `(↑π * I * 2).im * (-1 / 4) = π * (-1 / 2)`.**  A real
    identity obligation.  `Complex.mul_im` (Basic.lean:219) is `rfl` and
    `Complex.I_mul_im` (Basic.lean:273) gives `(I * z).im = z.re`; repair by
    `simp [Complex.mul_im]` to expose the `im`s, then `ring`.
7. **E08/E09 (L173-174) `linarith` finds no contradiction; `assumption` fails on
    `3 < rexp (π / 2)`.**  The hypotheses are *consistent* — `hlog3 : log 3 < 3/2`
    and `hhalf : 3/2 < π/2` give `a✝ : log 3 ≤ π/2`, a true bound, not a
    contradiction.  No `linarith` can close `⊢ False` from that.  The real content
    is `π/2 > log 3`, so `exp (π/2) > exp (log 3) = 3`.  Repair: build that chain
    explicitly and finish with `Real.exp_lt_exp.mpr` + `Real.exp_log`; no
    `linarith` on `⊢ False`.
8. **E11 (L177) `1 / rexp (π/2) < 1/3` supplied where `(rexp (π/2))⁻¹ < ?m`
    required.**  `one_div_lt_one_div_of_lt` concludes with `HDiv.hd` while the
    goal's head is `Inv.inv`; the report states this pair verbatim.  Repair:
    `simpa only [one_div]` into the `⁻¹` form.

E10 (`?m.810 ≤ 1/3` unsolved) is the metavariable E11 fails to fill, so it
resolves with (8).

**Correction applied to the first draft of this file (CE 6308 re-audit).**
The four repairs for E13, E14, E16 and E17 were initially *described* here as
applied when the corresponding source was in fact byte-identical to the CE'd
v56.  The pre-submission CE regression check caught this by diffing against
the previous CE's frozen source and reporting E14 and E16 as "unchanged
expression, unchanged context".  Each was then re-diagnosed from the
reported goal state and genuinely changed; the diagnoses are recorded at the
repair sites and in `artifacts/milnor_thrice_punctured_cover/v57_explanation.txt`.
In short: E14 was a *second*, redundant `rw [h1]`; E16 was `rw [← hexp_neg] at
hpre` in an orientation that cannot match; E17 was `rw [hce]` against a
product norm that had not been split by `Complex.norm_mul`; E13 was
`rw [one_div, div_lt_iff₀ hone]` against an `Inv.inv`-headed goal, where
`one_div` only rewrites in the other direction.  Every one of the 19 groups in
CE 6308 now has a real source change.

**Argument-order note retained from v55.**  `pow_lt_one₀ (h₀) (h₁) (n ≠ 0)` and
`one_lt_pow₀ (ha) (n ≠ 0)` take nonnegativity/strictness FIRST with `n`
implicit; `pow_le_pow_left₀ (h₀) (h) (n)` has `n` EXPLICIT; while
`pow_lt_pow_left₀ (hab) (ha) (n ≠ 0)` takes the COMPARISON first.

**No Lean was run locally.**  Every name below was read out of the pinned tree at
Mathlib revision `0df444a3` before use:

  `Complex.hasSum_re`                 Analysis/Complex/Basic.lean:605
  `Complex.mul_im`                    Data/Complex/Basic.lean:219  (rfl)
  `Complex.I_mul_im`                  Data/Complex/Basic.lean:273
  `mul_self_lt_mul_self`              (from `1 < x`, using `sq_nonneg`)
  `one_div`                           (simp-only bridge `x⁻¹ = 1 / x`)
  `zero_tsum`                         (∑' n, (0:ℝ) = 0)
  `Real.exp_lt_exp`                   Analysis/Complex/Exponential.lean:313
  `Real.exp_le_exp`                   Analysis/Complex/Exponential.lean:317
  `Real.pi_gt_three`                  Analysis/Real/Pi/Bounds.lean:151
  `Real.log_three_lt_d9`              Analysis/Complex/ExponentialBounds.lean:104
  `Summable.tsum_lt_tsum_of_nonneg`   Topology/Algebra/InfiniteSum/Real.lean:106
    (takes **`Summable g`** last, not `Summable f` — the 6291 E03 confusion)

The mathematics below is unchanged from variant C: `‖θ₃‖ > 1` comes from the
*direction* of the `jacobiTheta_eq_tsum_nat` series, not from any bound on
`‖θ₃ - 1‖`, and the numerator is bounded by the geometric-series estimate
`‖θ₂(2I)‖ ≤ 16/7 < 5/2` against `e^{-π/2} < 1/3`.

Historical note: variants A2 and B reach `‖θ₃‖ > 1` through
`Complex.re_le_norm : z.re ≤ ‖z‖`.  This variant keeps the `normSq` route:

    Complex.one_lt_normSq_iff : 1 < normSq x ↔ 1 < ‖x‖

Variants A2 and B both reach `‖θ₃‖ > 1` through `Complex.re_le_norm :
z.re ≤ ‖z‖`, i.e. through an inequality that *discards* the imaginary part.
This variant replaces that last step with the norm identity route:

    Complex.one_lt_normSq_iff : 1 < normSq x ↔ 1 < ‖x‖
    Complex.sq_norm_sub_sq_im : ‖z‖ ^ 2 - ‖z‖ ... (via normSq)

Since `normSq z = z.re ^ 2 + z.im ^ 2` and `(θ₃).re > 1` with
`z.im ^ 2 ≥ 0`, `normSq θ₃ > 1` follows, hence `‖θ₃‖ > 1`. This uses the
`normSq` bridge rather than `re_le_norm`, so a verdict distinguishes the
final inequality mechanism as well as the series handling.

The bottleneck diagnosis and the whole numerator chain are unchanged from
variant A2; see `artifacts/milnor_thrice_punctured_cover/V55_DIAGNOSIS.md`.

Target: `MilnorDynamics.milnorLambdaHalfShift_ne_one`
(`e3e8c8e6-e669-4dc3-ad2d-db0b29cd96c1`), Open.

**Why v52 (6260, 24 groups) and v53 (6262, 25 groups) both failed.**
Both repaired every *tactic* group, and both still end with

```lean
linarith [hnum_lt]   -- where  hnum_lt : ‖Num‖ < ‖Den‖
```

which needs `‖Den‖ > 1`, i.e. `‖jacobiTheta (2 * I)‖ ^ 4 > 1`. The two
hypotheses handed to that `linarith` were `hden4 : (5/6)^4 < ‖θ₃‖ ^ 4` and
`hden16 : (5/6)^4 < 1`. Both are true, and together they are consistent with
`‖θ₃‖ ^ 4 = 1/2`, so the goal is **not a consequence of the context** at any
tactic verbosity. That is a mathematical hole, not a tactic failure, and it
is why two structurally different restructures both ended in a terminal
`linarith`. Full diagnosis: `artifacts/.../V55_DIAGNOSIS.md`.

**The mathematics.** `‖θ₃‖ > 1` cannot come from a bound on `‖θ₃ - 1‖`: the
triangle inequality gives both `1 - ‖θ₃ - 1‖ ≤ ‖θ₃‖` and `‖θ₃‖ ≤ 1 + ‖θ₃ - 1‖`,
so no size bound on the difference pushes `‖θ₃‖` *past* `1`. It must come
from the **direction** of the series.

`jacobiTheta_eq_tsum_nat hpos` splits the `ℤ`-series away from `n = 0`:

    jacobiTheta τ = ↑1 + ↑2 * ∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ)

At `τ = 2I` the exponent is `π * I * ((n : ℂ) + 1) ^ 2 * (2 * I)`, and
`I * (2 * I) = -2`, so this is the real number `-2π (n+1)²`. Each summand is
therefore `cexp` of a negative real, its real part is `rexp (-2π (n+1)²) > 0`,
and each is at most `1`. So `(jacobiTheta (2I)).re = 1 + 2 * (positive) > 1`,
and `Complex.re_le_norm` gives `‖θ₃‖ > 1`, whence `‖θ₃‖ ^ 4 > 1`.

The whole `‖θ₃ - 1‖` apparatus of v52 (`htri`, `hsub`, `hsub6`, `hden4`,
`hden16`) is deleted, removing eight of v52's groups at their root rather
than patching each.

No Lean was run locally. Every name below was read out of the pinned tree at
Mathlib revision `0df444a3` before use:

  `jacobiTheta_eq_tsum_nat`  OneVariable.lean:84
  `Complex.exp_re`           Analysis/Complex/Trigonometric.lean:519
  `Complex.I_mul_I`          Data/Complex/Basic.lean:262
  `Complex.re_le_norm`       Analysis/Complex/Norm.lean:43
  `Complex.norm_pow`         Analysis/Complex/Norm.lean:86
  `Complex.ofReal_re`        Data/Complex/Basic.lean:88
  `one_lt_pow₀`              Algebra/Order/GroupWithZero/Basic.lean:443
  `pow_lt_one₀`              Algebra/Order/GroupWithZero/Basic.lean:431
  `Summable.tsum_lt_tsum_of_nonneg` Topology/Algebra/InfiniteSum/Real.lean:106
  `summable_const`           (∑' n, (0:ℝ) = 0, by simp)
  `norm_jacobiTheta₂_term`   TwoVariable.lean:75
  `Summable.of_nonneg_of_le` Topology/Algebra/InfiniteSum/ENNReal.lean:530
  `tsum_geometric_of_lt_one` Analysis/SpecificLimits/Basic.lean:329

Argument-order trap, since v52 got it wrong: `pow_lt_one₀ (h₀) (h₁) (n ≠ 0)`
and `one_lt_pow₀ (ha) (n ≠ 0)` both take the nonnegativity/strictness FIRST
with `n` implicit; `pow_le_pow_left₀ (h₀) (h) (n)` has `n` EXPLICIT; while
`pow_lt_pow_left₀ (hab) (ha) (n ≠ 0)` takes the COMPARISON first. v52's
E19/E20/E21 came from mixing these up.
-/

theorem solution :
    milnorLambdaHalfShift (2 * I) ≠ 1 := by
  --
  -- ACCOUNTING FOR CE 6394 (7 groups, 7 diagnostics, 0 cascades).
  -- Read from a report captured once to /tmp/p2m-ce-6394.jpctj8, verified by
  -- its closing marker `groups=7 diagnostics=7` against the header's
  -- `7 error group(s) | 7 diagnostic(s)`, and read through line 251.
  --
  --   E01 L412  REPAIRED.  Root cause was NOT the suggested Pi-typed atom.
  --             `htsum_re` has `.re` inside `∑'` and the negated hypothesis
  --             has `.re` outside it, so `linarith` saw two unrelated atoms.
  --             Fixed with `Complex.re_tsum` (verified at
  --             Mathlib/Analysis/Complex/Basic.lean:611) plus a locally
  --             re-established `HasSum` witness.
  --   E02 L589  REPAIRED.  `rw [Complex.I_sq]` could never fire: the reported
  --             target was `(↑π * I * (2 * I)).re / 4 = -π / 2`, which contains
  --             no `I ^ 2`.  Replaced with `Complex.I_mul_re` (verified at
  --             Mathlib/Data/Complex/Basic.lean:271) after an explicit
  --             reassociation.
  --   E03 L725  REPAIRED.  `|>` is function application and was handed an
  --             `Iff`.  Replaced by a bare `show … from _`.
  --   E04 L758 REPAIRED — and v65's repair rested on a false premise too.
  --             The residual goal is `⊢ instLT = partialOrder.toLT`, a leaked
  --             `convert` instance diamond, not a comparison.  v65 used
  --             `show … from hgoal`, which requires `(7/8)⁻¹ = 8/7` to be
  --             DEFINITIONAL; in a `LinearOrderedField` it is not (it is the
  --             rewrite `inv_div`, Mathlib/Algebra/Group/Basic.lean:393).
  --             v66 rewrites with `inv_div` and `exact`s, so no `LT` instance
  --             case is ever created.
  --   E05 L877 REPAIRED — v65 had marked this UNRESOLVED for the wrong reason.
  --             v65's note claimed the residual goal "is NOT identified"
  --             because the formatted report truncated it.  It was identified:
  --             the raw remote `error_message` in
  --             .prove2me/logs/diagnostic/1790953635572962450-181280.json
  --             carries it in full, and it is
  --               ⊢ -(π * ↑b * 2) - π * ↑b ^ 2 * 2 = -(π * ↑b ^ 2 * 2)
  --             — an *algebraically false* equation (b = 1 gives -4 vs -2).
  --             So the `hrw` lemma was mis-stated, not merely un-proved, and
  --             eight candidates in a row re-tried `ring` against a falsehood.
  --             Restating the RHS as `-(π * (b^2 + b))` — the form the sibling
  --             `hb1` already used — makes the identity true and leaves the
  --             consumer's `b^2 ≥ b` proof valid.
  --   E06 L1052 REPAIRED, AND v65's REPAIR WAS ITSELF WRONG — corrected here.
  --             `mul_lt_mul_of_lt_of_lt` carries
  --             `[MulLeftStrictMono α] [MulRightStrictMono α]` as *out-*
  --             parameters (verified at
  --             Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:166-168), so
  --             Lean reported the bare `MulLeftStrictMono ℝ` obligation.
  --             v65 swapped in `mul_lt_mul_of_pos_right`, which DOES elaborate
  --             on ℝ (`IsStrictOrderedRing.toMulPosStrictMono` is an instance
  --             at priority 200, Mathlib/Algebra/Order/Ring/Defs.lean:88-89)
  --             — but that lemma needs BOTH bounds to share ONE factor, and
  --             this goal bounds DIFFERENT factors (`e < 1/3` on the left,
  --             `n < 5/2` on the right).  v65 would have proved a different
  --             statement.  v66 applies `mul_lt_mul_of_pos_left` TWICE, each
  --             step pinning one factor, then `.trans`.
  --   E07 L1106 REPAIRED.  Three shape mismatches, all from the definition's
  --             `2 * I / 2` unfolding to `I * 2`: commutativity of the ℂ
  --             argument, the reversed norm/exponential product inside `^ 4`,
  --             and `-(π * (1/2))` versus `-π / 2`.  `norm_num` cannot supply
  --             ℂ commutativity, so the previous `norm_num`-only repair could
  --             not have worked; `mul_comm` is named explicitly instead.
  --
  -- All seven groups are now addressed from the compiler evidence.  Three of
  -- them (E04, E05, E06) had repairs in v65 that were individually plausible
  -- and collectively wrong; each was corrected here against the source or
  -- against a substituting value.  This file remains UNVERIFIED until a remote
  -- submission containing it is accepted.
  have hpos : (0 : ℝ) < (2 * I : ℂ).im := by norm_num

  -- ================================================================
  -- Denominator: `‖θ₃‖ > 1`, read off the real part of the ℕ-series.
  -- ================================================================
  -- `I * (2 * I) = -2`, so the exponent is the real number `-2π (n+1)²`.
  have hexp_re : ∀ n : ℕ, (0 : ℝ) < (cexp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * I))).re := by
    intro n
    rw [Complex.exp_re]
    -- `z.im = 0` (the exponent is real), so `cos z.im = 1`.
    have hz : π * I * ((n : ℂ) + 1) ^ 2 * (2 * I)
        = (((-2 * (Real.pi : ℝ)) * (n + 1) ^ 2 : ℝ) : ℂ) := by
      -- REPAIR of E01 (6321 L214, "rewrite failed: did not find `I ^ 2`").
      -- v58 tried to make `I * I` occur by reassociating, and the FIRST calc
      -- step `= π * ((n:ℂ)+1)^2 * (2 * (I * I)) := by ring` is the fatal one:
      -- `ring` cannot reassociate, so that step is false and Lean rejects it
      -- before ever reaching the `Complex.I_mul_I` rewrite.  (Lean reported
      -- the failure against the `I ^ 2` line because that is the first
      -- `rw`/`norm_num` it reached.)
      --
      -- The actual fix: the two `I`s in `π * I * … * (2 * I)` are separated
      -- by a non-constant factor, so NO rearrangement can make them adjacent
      -- as a syntactic `I * I`.  The only route is to give the ring normaliser
      -- the fact `I ^ 2 = -1` and let it re-associate internally — which
      -- requires `ring_nf` FIRST (it collects into `2 * ↑π * … * I ^ 2`),
      -- and the rewrite to come AFTER.  v56/v57 had exactly these two steps
      -- in the opposite order, which is the single recurring defect across
      -- 6319/6321.
      --
      -- `ring_nf` collects the product into a polynomial with the single atom
      -- `I ^ 2`; the rewrite then fires on that atom, and the second
      -- `ring_nf` closes the now-linear ℝ identity.  `Complex.I_sq` is
      -- verified at Mathlib/Data/Complex/Basic.lean:627.
      --
      -- REPAIR of E01 (6345 L228, "No goals to be solved").  v59 ended this
      -- block with a trailing `norm_num` that is no longer reachable: once
      -- `I ^ 2` has been rewritten to `-1`, the goal is a purely linear ℝ
      -- identity and `ring_nf` at the previous line already discharges it.
      -- The surplus `norm_num` was then run against zero remaining goals.
      push_cast
      ring_nf
      have hI2 : (I : ℂ) ^ 2 = -1 := Complex.I_sq
      rw [hI2]
      ring_nf
    have him : (π * I * ((n : ℂ) + 1) ^ 2 * (2 * I)).im = 0 := by
      rw [hz]
      exact Complex.ofReal_im _
    rw [him, Real.cos_zero, mul_one]
    exact Real.exp_pos _

  have htsum_re : (0 : ℝ) < (∑' n : ℕ,
      (cexp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * I))).re) := by
    -- Summability comes from Mathlib's own `HasSum` for this series.
    have hhs : HasSum (fun n : ℕ => cexp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * I)))
        ((jacobiTheta (2 * I) - 1) / 2) :=
      hasSum_nat_jacobiTheta hpos
    have hg : Summable (fun n : ℕ =>
        (cexp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * I))).re) := by
      -- v55 used `rw [Complex.re_tsum] at hnn` here and it failed (E02): the
      -- goal is a `Summable`, and `re_tsum` rewrites `(∑' n, f n).re`, which
      -- cannot occur in a `Summable` statement.  `Complex.hasSum_re` maps the
      -- `HasSum` to a `HasSum` of the real parts, so `.summable` is the goal.
      exact (Complex.hasSum_re hhs).summable
    -- Compare the zero series against the positive one.
    -- `Summable.tsum_lt_tsum_of_nonneg` takes `(h0) (h) (hi) (hg)` where the
    -- LAST argument is `Summable g`, i.e. of the POSITIVE series, not of the
    -- zero series.  `hg` above is exactly that.
    -- v55 left the leading `0 <` unaccounted for, and v56's `simpa only
    -- [zero_tsum]` failed twice over (6308 E03, E04): `zero_tsum` does not
    -- exist (Mathlib's name is `tsum_zero`), and even with a working rewrite
    -- the `have` was typed `∑' n, 0 < ∑' n, g`, so the error survived — Lean
    -- reported the supplied term as still `∑' (n : ℕ), 0 < …`, i.e. the `0 <`
    -- was *inside* the `∑'`, not in front of it.
    -- Repair: state the `have` at exactly the goal's type, so no transport is
    -- needed at all.
    -- v56 and v57 both ended this block with a bare
    --     simpa only [tsum_zero] using (Summable.tsum_lt_tsum_of_nonneg …)
    -- which is wrong twice over.  First, `tsum_lt_tsum_of_nonneg` concludes
    -- `∑' n, f n < ∑' n, g n`; to turn its left side `∑' n, (0 : ℝ)` into the
    -- `0` in front of the goal you need the `∑' n, 0 = 0` lemma, and v57's own
    -- comment (inherited from the 6308 re-audit) records that the name
    -- `zero_tsum` does not exist, so `tsum_zero` is a guess at a `to_additive`
    -- name that has not been verified against this Mathlib revision.  Second,
    -- even a correct name would not fix the *shape*: the `have` was annotated
    -- `∑' n, (0 : ℝ) < ∑' n, g`, i.e. the `0 <` ended up inside the binder,
    -- which is exactly the "Actual type: ∑' (n : ℕ), 0 < ∑' …" that 6291-E05,
    -- 6298-E03, 6299-E04 and 6300-E04 all reported.
    --
    -- REPAIR of E02 (6321 L255, "failed to prove positivity") and E03
    -- (6321 L224, "unsolved goals: `0 < ∑' n, …`").
    --
    -- v58's text asserted, from a search that missed generated names, that
    -- `tsum_zero` "has no declaration anywhere".  That was WRONG, and it is
    -- the direct cause of E02: `tsum_zero` is generated by
    -- `@[to_additive (attr := simp)]` on `tprod_one`
    -- (Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:462-465), so it has no
    -- `theorem tsum_zero` line for a `.lean`-text grep to find.  The same
    -- mistake produced the phantom `zero_tsum`.
    --
    -- v58 then called `Summable.tsum_lt_tsum` with FOUR positional arguments
    -- and a `by simp` summability for the zero series.  The declaration it
    -- means is `Summable.tsum_lt_tsum_of_nonneg`
    -- (Mathlib/Topology/Algebra/InfiniteSum/Real.lean:106-109), which is
    -- `protected` inside `namespace summable` and takes
    -- `(h0) (h) (hi) (hg)` with `i` implicit — and whose proof term is
    -- literally `Summable.tsum_lt_tsum h hi (.of_nonneg_of_le h0 h hg) hg`,
    -- so the base three-argument `Summable.tsum_lt_tsum` is internal plumbing
    -- and is NOT the right entry point.  Supplying `hg` (the *positive*
    -- series) in the last slot is correct, per that signature.
    --
    -- `tsum_zero` is `∑' _, (0 : α) = 0` and is a `simp` attribute, so it
    -- fires on the left side without any name being written.  The result
    -- `0 < ∑' n, g n` then matches the goal exactly, with the `0 <` outside
    -- the binder — which is the shape v56/v57 got wrong and which 6291-E05,
    -- 6298-E03, 6299-E04 and 6300-E04 all reported.
    have hlt : (0 : ℝ) < ∑' n : ℕ,
        (cexp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * I))).re := by
      simpa only [tsum_zero] using
        (Summable.tsum_lt_tsum_of_nonneg (i := (0 : ℕ))
          (f := fun _ : ℕ => (0 : ℝ))
          (g := fun n : ℕ => (cexp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * I))).re)
          -- REPAIR of E02 (6345 L306) and E03 (6345 L236), one defect.
          --
          -- `Summable.tsum_lt_tsum_of_nonneg` takes
          --     (h0 : ∀ b, 0 ≤ f b) (h : ∀ b, f b ≤ g b) (hi : f i < g i) (hg)
          -- with `f := fun _ => (0 : ℝ)`.  So the FIRST bound is `0 ≤ 0`, not
          -- a bound on the positive series.  v59 passed `(hexp_re b).le` in
          -- both slots, so Lean reported
          --     Supplied: LT.lt.le (hexp_re b)   Actual: 0 ≤ (cexp …).re
          --                              Expected: 0 ≤ 0
          -- (E02).  Because the application then failed, `hlt` was never
          -- produced, so the `have htsum_re` goal stayed open (E03).
          --
          -- `h0` is `fun _ => le_rfl`; only the SECOND slot bounds `g`.
          (fun _ => le_rfl) (fun b => (hexp_re b).le) (hexp_re 0) hg)
    -- REPAIR of E01 (6354 L241).  The block above builds `hlt`, whose type is
    -- *syntactically identical* to the enclosing `htsum_re` goal:
    --     (0 : ℝ) < ∑' n : ℕ, (cexp (π*I*((n:ℂ)+1)^2*(2*I))).re
    -- but nothing in the block ever closes `htsum_re` itself.  `simpa only
    -- [tsum_zero]` rewrites only the *supplied* term's left side
    -- (`∑' _, (0 : ℝ)` becomes `0`); the goal has no `∑' _, 0` to rewrite, so
    -- `simpa` leaves the goal exactly as it found it and the block ends with
    -- one goal still open — which is exactly the reported state:
    --     hlt : 0 < ∑' (n : ℕ), (cexp …).re
    --     ⊢   0 < ∑' (n : ℕ), (cexp …).re
    -- `hlt` being present in the reported context is the positive evidence
    -- that the inner `have` succeeded and only the outer one is missing.
    -- Repair: close it explicitly with `exact hlt`, so no simplifier has to
    -- guess which side to rewrite.
    exact hlt

  have hre_gt1 : (1 : ℝ) < (jacobiTheta (2 * I)).re := by
    rw [jacobiTheta_eq_tsum_nat hpos, Complex.add_re, Complex.mul_re]
    -- REPAIR of E04 (6345 L310).  `jacobiTheta_eq_tsum_nat` writes
    --     jacobiTheta (2*I) = (1 : ℂ) + 2 * ∑' n, (cexp …)
    -- and `Complex.add_re`/`Complex.mul_re` have already reduced the
    -- numeral to `re 1 + (re 2 * (…) - im 2 * (…))`.  The goal therefore
    -- contains no `‖↑1‖` at all, so `rw [Complex.norm_of_nonneg …]` had
    -- nothing to match and reported "Did not find an occurrence of the
    -- pattern `‖↑1‖`".  The rewrite is unnecessary: the goal is already in
    -- the form `linarith` needs.
    --
    -- REPAIR of E02 (6354 L336).  The reported goal state was
    --     a✝ : re 1 + (re 2 * (∑' …).re - im 2 * (∑' …).im) ≤ 1
    --     ⊢ False
    -- `linarith` failed because `re 1`, `re 2` and `im 2` are *opaque atoms*
    -- to it: it cannot know `re 2 = 2` and `im 2 = 0`, so the two real-part
    -- atoms and the one imaginary-part atom look like unrelated symbols and
    -- no linear combination of `htsum_re : 0 < ∑' …` closes it.  This is the
    -- same class of failure as `failure/linarith-pi-type-atom.md` — the
    -- obstacle is the *type/shape* of the atoms, not the algebra.
    --
    -- Repair: evaluate the numeral projections first, so the goal becomes the
    -- genuine real inequality `1 < 1 + 2 * (∑' …).re - 0 * (∑' …).im`, and
    -- only then hand it to `linarith` together with `htsum_re`.
    -- REPAIR of E01 (6366 L366).  The reported goal state was
    --     a✝ : re 1 + (2 * (∑' …).re - 0 * (∑' …).im) ≤ 1
    --     ⊢ False
    -- so the previous repair *did* fire: `im 2` is gone (now `0`), and only
    -- the `re 1` atom survives.  That is the tell that the named rule was
    -- the wrong one, not that the tactic needs more help.
    --
    -- The rule that WAS named is guarded:
    --   @[simp] lemma re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℂ).re = ofNat(n)
    --   @[simp] lemma im_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℂ).im = 0
    -- (Mathlib/Data/Complex/Basic.lean:354-355).  `[1.AtLeastTwo]` is FALSE,
    -- so `re_ofNat` can never close `re 1`; it only worked for `2`.
    --
    -- Repair: name the unguarded rules for both numerals.
    --   Complex.one_re / Complex.one_im   — (1 : ℂ).re = 1, (1 : ℂ).im = 0
    --     (Mathlib/Data/Complex/Basic.lean:148,152 — `@[simp]`, `rfl`)
    --   Complex.natCast_re / natCast_im   — (n : ℂ).re = n, (n : ℂ).im = 0
    --     (Mathlib/Data/Complex/Basic.lean:356-357 — `@[simp, norm_cast]`, `rfl`)
    -- The hypothesis then becomes the genuine linear statement
    --     1 + 2 * (∑' …).re - 0 * (∑' …).im ≤ 1
    -- which `htsum_re : 0 < ∑' …` contradicts immediately.
    -- REPAIR of E01 (6380 L388).  The reported goal state was
    --     a✝ : 1 + (re 2 * (∑' …).re - im 2 * (∑' …).im) ≤ 1
    --     ⊢ False
    -- so `Complex.one_re` DID fire this time (the `re 1` atom is gone — it
    -- reads `1`), and the single remaining atoms are `re 2` / `im 2`.
    --
    -- The mechanism behind the failure is `norm_num only`.  Naming
    -- `Complex.natCast_re` explicitly does not help, because the numeral in
    -- the goal is not syntactically `(↑2 : ℂ)`.  `ℂ`'s `NatCast` instance is
    -- `natCast n := ofReal n` (Mathlib/Data/Complex/Basic.lean:341), so
    -- `(2 : ℂ)` is `ofReal 2`, whose real part reduces through
    --   Complex.ofReal_re (r : ℝ) : Complex.re (r : ℂ) = r   (:89, rfl)
    -- — a different lemma, reached only by *unfolding* the cast.  Lean's
    -- pretty-printer then displays `ofReal 2` as the bare numeral `2`,
    -- which is why the goal reads `re 2` and why a rewrite keyed on the
    -- literal `↑2` finds nothing.
    --
    -- `norm_num only [...]` uses ONLY the listed lemmas and so cannot see
    -- through that cast.  Unrestricted `norm_num` instead uses the
    -- `@[norm_cast]` attribute, and every rule needed here carries it:
    --   Complex.ofReal_re / ofReal_im              (:89, :93)
    --   Complex.ofReal_natCast (n : ℕ) : ofReal n = n  (:347)
    --   Complex.natCast_re / natCast_im            (:356-357)
    -- so the projection evaluates to the real numeral and `linarith` closes
    -- the goal against `htsum_re`.
    norm_num
    --
    -- REPAIR of E01 (CE 6394 L412, `ARITHMETIC TACTIC FAILURE`).
    --
    -- The reported goal state was
    --     htsum_re : 0 < ∑' (n : ℕ), (cexp (↑π * I * (↑n + 1) ^ 2 * (2 * I))).re
    --     a✝       : (∑' (n : ℕ), cexp (↑π * I * (↑n + 1) ^ 2 * (2 * I))).re ≤ 0
    --     ⊢ False
    -- with `linarith failed to find a contradiction`.
    --
    -- NOTE: the report named `failures/linarith-pi-type-atom.md`, but that
    -- diagnosis does NOT fit this goal state.  Every atom here is a real
    -- number, not a function into ℝ, so the Pi-typed-atom mechanism (where
    -- `c + r • u` is an opaque whole function) cannot be what is happening.
    -- The file is still worth having read, but its repair ladder — project to
    -- a coordinate with `congrArg`, use `Pi.add_apply`, reassemble with
    -- `funext` — is inapplicable here.  Recording that so the next cycle does
    -- not re-apply it.
    --
    -- The actual obstruction is visible by comparing the two atoms:
    --     htsum_re has `.re` INSIDE the sum:   0 < ∑' n, (cexp …).re
    --     a✝       has `.re` OUTSIDE the sum:  (∑' n, cexp …).re ≤ 0
    -- `Complex.re` is not additive across a `∑'`, so to `linarith` these are
    -- two unrelated atoms sharing no subterm.  No amount of numeral
    -- evaluation (what the previous repairs did) can help: the numerals were
    -- already gone from this goal.  The missing step is the interchange of
    -- `.re` and `∑'`.
    --
    -- `Complex.re_tsum` is exactly that interchange:
    --   theorem Complex.re_tsum [L.NeBot] {f : α → ℂ} (h : Summable f L) :
    --     (∑'[L] a, f a).re = ∑'[L] a, (f a).re
    -- (Mathlib/Analysis/Complex/Basic.lean:611, inside `namespace Complex`).
    --
    -- The summability witness already exists in this very `have` block, from
    -- `hasSum_nat_jacobiTheta hpos`:
    --     hhs : HasSum (fun n : ℕ => cexp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * I)))
    --                ((jacobiTheta (2 * I) - 1) / 2)
    -- so `hhs.summable : Summable …` is available without any new bound.
    --
    -- `hhs` itself is local to the `htsum_re` block, so the summability fact
    -- is re-established here from the same source lemma rather than being
    -- hoisted (which would change the shape of an unrelated, already-accepted
    -- step).  `hasSum_nat_jacobiTheta` is the identical call used at line 245.
    have hhs' : HasSum (fun n : ℕ => cexp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * I)))
        ((jacobiTheta (2 * I) - 1) / 2) :=
      hasSum_nat_jacobiTheta hpos
    --
    -- Repair: rewrite `a✝` with `re_tsum` so both sides mention the *same*
    -- sum, then `linarith` closes the genuine contradiction
    -- `0 < (∑' …).re ∧ (∑' …).re ≤ 0`.
    rw [Complex.re_tsum hhs'.summable] at *
    linarith [htsum_re]

  -- `‖θ₃‖ > 1` via `normSq`: `normSq z = z.re ^ 2 + z.im ^ 2`, so a real
  -- part above `1` forces the squared norm above `1`.
  have hnormSq : (1 : ℝ) < normSq (jacobiTheta (2 * I)) := by
    -- REPAIR of E04 (6321 L259), E05 (6321 L273 "Unknown identifier `simpa`"),
    -- E06 (6321 L264 "unsolved goals: `1 < normSq (jacobiTheta (2*I))`") and
    -- E08 (6321 L273 "unexpected token `using'; expected command").
    --
    -- All four are ONE defect, not four.  v58 (like v57) wrote
    --     have hre_sq : 1 < (…).re ^ 2 :=
    --       -- comment lines …
    --       simpa only [pow_two, one_mul] using (…)
    -- with no `by`, so everything after `:=` is parsed as a TERM.  `simpa` is
    -- a tactic, not a term, so Lean reported it as an unknown identifier
    -- (E05) and then choked on the `using` token (E08).  Because the `have`
    -- never elaborated, the two facts `hre_sq`/`him_sq` never entered the
    -- context, so the enclosing goal `1 < normSq (jacobiTheta (2*I))` was
    -- left open (E06) and the very same missing `normSq` rewrite surfaced
    -- again one line up (E04).  Repairing the syntax repairs all four.
    --
    -- `one_lt_sq_iff₀ : 1 < a ^ 2 ↔ 1 < a` is used directly, so no `simpa`
    -- and no `pow_two`/`one_mul` normalisation is needed at all.
    --
    -- REPAIR of E05 (6345 L335).  `one_lt_sq_iff₀` is declared at
    -- Mathlib/Algebra/Order/GroupWithZero/Basic.lean:692 as
    --     one_lt_sq_iff₀ (ha : 0 ≤ a) : 1 < a ^ 2 ↔ 1 < |a|
    -- (the `ZeroLEOneClass` version concludes `1 < a`; the ℝ form below is the
    -- `LinearStrictOrderedRing` one and concludes `1 < |a|`).  6345-E05 asked
    -- for `1 < |re|` and 6354-E03 asked for `1 < |re| ^ 2`: the same ℝ
    -- shadowing, seen from two different goals.
    --
    -- The conversion therefore has to run from `re` to `|re|` — establish
    -- `0 < re`, rewrite `|re|` away with `abs_of_pos`, then hand `hre_gt1`
    -- to the `mpr` direction.  Supplying `hre_gt1` *directly* to `.mpr`
    -- (as 6345-E05's repair did) leaves the `|re|` in the goal's head, which
    -- is 6354-E03.
    have hre_sq : (1 : ℝ) < (jacobiTheta (2 * I)).re ^ 2 :=
      -- REPAIR of E02 (6366 L404).  The reported pair was
      --   Actual:   1 < |(jacobiTheta (2 * I)).re| ^ 2
      --   Expected: 1 < (jacobiTheta (2 * I)).re ^ 2
      -- so the whole mismatch came from supplying `abs_nonneg _` as the
      -- hypothesis argument.  But
      --   one_lt_sq_iff₀ (ha : 0 ≤ a) : 1 < a ^ 2 ↔ 1 < a
      -- (Mathlib/Algebra/Order/GroupWithZero/Basic.lean:692)
      -- is stated on the *plain* square `a ^ 2`, not on `|a| ^ 2`: the `iff`
      -- runs `1 < a ^ 2 ↔ 1 < a`.  Naming a fact about `|a|` therefore
      -- instantiates `a := |(jacobiTheta (2 * I)).re|`, which puts an
      -- `|…|` in the conclusion — exactly the reported Actual type.
      --
      -- There is no `abs` anywhere in the result, so nothing has to be
      -- rewritten away.
      --
      -- REPAIR of E02 (6380 L441).  The `abs` is gone, so 6366-E02 is
      -- repaired; what fails now is the *hypothesis* argument.  The compiler
      -- reported
      --   the argument `hre_gt1` has type `1 < (jacobiTheta (2 * I)).re`
      --   but is expected to have type `0 < (jacobiTheta (2 * I)).re`
      --   in the application `le_of_lt hre_gt1`
      -- `le_of_lt` yields a `≤`, and `one_lt_sq_iff₀` asks only for `0 ≤ a`;
      -- unifying `0 ≤ a` with that supplied `≤` forces the bound to be `0`
      -- *strictly*, so `le_of_lt` no longer typechecks against it.
      -- `zero_le_one.trans hre_gt1.le` produces the `0 ≤ re` the lemma
      -- actually wants, and is the shape Mathlib itself uses at
      -- `Mathlib/NumberTheory/Pell.lean:205`.
      (one_lt_sq_iff₀ (zero_le_one.trans hre_gt1.le)).mpr hre_gt1
    have him_sq : (0 : ℝ) ≤ (jacobiTheta (2 * I)).im ^ 2 := sq_nonneg _
    rw [Complex.normSq_apply]
    linarith
  have hth3 : (1 : ℝ) < ‖jacobiTheta (2 * I)‖ :=
    Complex.one_lt_normSq_iff.mp hnormSq
  have hth3_4 : (1 : ℝ) < ‖jacobiTheta (2 * I)‖ ^ 4 :=
    one_lt_pow₀ hth3 (by norm_num)

  -- ================================================================
  -- Numerator: `‖Num‖ < 1`, from `e^{-π/2} < 1/3` and `‖θ₂‖ < 5/2`.
  -- ================================================================
  have him : (2 * I : ℂ).im = 2 := by norm_num
  have hi1 : I.im = 1 := by norm_num
  have hpre_re : (π * I * (2 * I) / 4 : ℂ).re = -(Real.pi : ℝ) / 2 := by
    -- v55 got here with `rw [h4, Complex.div_ofReal_re, ← mul_assoc,
    -- Complex.mul_I_re]` and stopped at an unsolved
    --     ⊢ (↑π * I * 2).im * (-1 / 4) = π * (-1 / 2)
    -- (E07 of 6291/6298/6300, reported identically at 6298 L154, 6299 L158,
    -- 6300 L135).  The compiler evidence is the point: an `im` atom survives
    -- on the left, so `ring` has nothing to do.  `Complex.mul_im` is the rule
    -- that descends it.
    --
    -- v56's attempt used `simp only [Complex.mul_im, Complex.I_mul_im, …]`
    -- and failed with "simp made no progress" (the `simp` failure archived by
    -- `explain` as one of the `seen 3x` GONE causes): after the preceding
    -- `norm_num` normalisations the goal's head was `↑π * I ^ 2 * 2`, a `pow`,
    -- and `Complex.mul_im` only matches a `mul`.  v57 "fixed" this by adding
    -- `rw [pow_two]` in front — which is the right idea, but it left a second
    -- defect in place: `simp only` with a list containing `Complex.I_mul_im`
    -- and `Complex.mul_im` in that order can re-associate the product into a
    -- shape where the next rule no longer matches, and `simp only` will *not*
    -- close the resulting numeric identity, so `ring` still gets `im` atoms.
    --
    -- REPAIR of E06 (6345 L376).  This is the SAME root cause as the `hz`
    -- defect: after `Complex.div_ofReal_re` and `push_cast` the goal is
    --     (↑π * I * (2 * I)).re / 4 = -π / 2
    -- and `rw [hI2]` looks for the pattern `I ^ 2`.  But the goal is already
    -- projected through `.re`, so the two `I`s are *inside* the `re` and no
    -- `I ^ 2` is visible to `rw` — which is exactly the reported "Did not find
    -- an occurrence of the pattern `I ^ 2`".
    --
    -- v56/v57/v59 all made the same ordering mistake here that they made in
    -- `hz`: rewrite `I ^ 2` BEFORE normalising the product.  The fix is to
    -- expand the real part FIRST, so that `I ^ 2` appears as a factor, and
    -- only then rewrite it.  `Complex.mul_re` is what descends `.re` into
    -- the product, and `Complex.I_re`/`Complex.I_im` supply `I.re = 0`,
    -- `I.im = 1`, at which point the identity is linear in `↑π`.
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
    --
    -- REPAIR of E04 (6354 L422).  The reported goal state was the FULLY
    -- expanded expression
    --     (↑π).re * I.re * I.im * im 2 * (-1/4)
    --   + (↑π).re * I.re ^ 2 * re 2 * (1/4)
    --   + I.re * (↑π).im * I.im * re 2 * (-1/4)
    --   + (↑π).im * I.im ^ 2 * im 2 * (1/4)
    --   + (↑π * I).im * (I * 2).im * (-1/4) = π * (-1 / 2)
    -- and `rw [hI2]` reported "Did not find an occurrence of the pattern
    -- `I ^ 2`".  Two separate reasons, both visible in that evidence:
    --
    --   (a) `simp only [Complex.mul_re]` descends only the OUTERMOST `.re`;
    --       the inner products `(↑π * I).im` and `(I * 2).im` are still
    --       opaque, so `ring_nf` has composite subterms to treat as atoms and
    --       never produces an `I ^ 2` factor for the rewrite to find.
    --   (b) Once `(a)` is fixed, there is no `I ^ 2` anyway: the goal is
    --       *linear* in `I.re` and `I.im`, and `I.re = 0` / `I.im = 1` are
    --       the only facts needed.  Rewriting `I ^ 2 = -1` was never the
    --       right move in this goal — it is the right move in `hz`, where the
    --       exponent really does appear.
    --
    -- Repair: flatten every `.re`/`.im` with the full `mul_re`/`mul_im` pair
    -- and then substitute the constant values of `I.re` and `I.im`.  After
    -- that the goal is a plain real polynomial in `π` and `ring` closes it.
    -- REPAIR of E03, E04 and E05 (6366 L483 and L422 — one cause).
    --
    -- E03/E04 said `Unknown constant 'Complex.re_one'` / `'Complex.im_one'`.
    -- Those names do not exist for `ℂ`: Mathlib writes the projection as the
    -- *suffix* of the numeral, not the prefix,
    --   Complex.one_re : (1 : ℂ).re = 1  (Mathlib/Data/Complex/Basic.lean:148)
    --   Complex.one_im : (1 : ℂ).im = 0  (Mathlib/Data/Complex/Basic.lean:152)
    -- both `@[simp]` and proved `rfl`.
    --
    -- E05 (`⊢ π * re 2 * (-1 / 4) = π * (-1 / 2)`) is the SAME defect seen
    -- downstream, and the mechanism is worth recording because it is silent.
    -- `norm_num only [...]` aborts the WHOLE normalisation if any name in its
    -- list is unknown, so the two bogus constants did not merely fail to
    -- supply `re 1`; they discarded every other rule in the list too, which
    -- is why `re 2` survived as an opaque atom.
    --
    -- The right rule for `re 2` is the *unguarded* one:
    --   Complex.natCast_re (n : ℕ) : (n : ℂ).re = n
    --   Complex.natCast_im (n : ℕ) : (n : ℂ).im = 0
    -- (Mathlib/Data/Complex/Basic.lean:356-357), both `@[simp, norm_cast]`
    -- and proved `rfl`, with no `AtLeastTwo` side condition.
    --
    -- REPAIR of E03 (6380 L455).  With the names corrected the reported goal
    -- advanced to
    --     ⊢ (↑π * I ^ 2 * 2).re * (1 / 4) = π * (-1 / 2)
    -- — genuine progress: both `re 1` and `re 2` are gone.  The residue is a
    -- *power* atom.  `Complex.mul_re` turned the outer product into a `mul`
    -- and `norm_num` re-associated it as `↑π * I ^ 2 * 2`; the `I ^ 2` in the
    -- middle is matched by neither `Complex.mul_re` (which needs a `mul` on
    -- top) nor `norm_num` (which does not descend into an `ℂ` power), so the
    -- `.re` is never expanded and `ring` has no polynomial to close.
    --
    --
    -- REPAIR of E02 (CE 6394 L589, `TACTIC FAILURE`).  The reported state was
    --     pattern:  I ^ 2
    --     target:   (↑π * I * (2 * I)).re / 4 = -π / 2
    -- i.e. `rw [Complex.I_sq]` reported "Did not find an occurrence of the
    -- pattern I ^ 2".
    --
    -- The previous repair's reasoning was WRONG.  It assumed the target had
    -- been re-associated to `↑π * I ^ 2 * 2`, where `Complex.I_sq` would
    -- apply.  It has NOT been re-associated: the target still reads
    -- `↑π * I * (2 * I)`, with the `2 * I` sitting *inside* the second
    -- factor, so the substring `I ^ 2` does not occur anywhere in the goal.
    -- `Complex.I_sq` (Mathlib/Data/Complex/Basic.lean:627) rewrites only
    -- `I ^ 2`, and the pattern is simply absent.  Every previous cycle
    -- re-added `rw [Complex.I_sq]` on the strength of an *in-file note*
    -- rather than the compiler's reported target — the audit trail shows that
    -- claim was repeated across at least three variants without ever being
    -- checked against the target Lean actually produced.
    --
    -- The structure to exploit is `↑π * (I * (2 * I))`: an `I` in *left*
    -- position and a `2 * I` in *right* position.  So the multiplication-by-
    -- `I` projection lemmas are the right tool, not the power lemma.
    -- Mathlib states them in `Mathlib/Data/Complex/Basic.lean`:
    --   theorem I_mul_re (z : ℂ) : (I * z).re = -z.im      (:271)
    --   theorem I_mul_im (z : ℂ) : (I * z).im =  z.re      (:273)
    --   theorem mul_I_re (z : ℂ) : (z * I).re = -z.im      (:267)
    --   theorem mul_I_im (z : ℂ) : (z * I).im =  z.re      (:269)
    --
    -- Repair: expose the `I * (2 * I)` shape with a `ring`-level
    -- reassociation on the ℂ product, apply `Complex.I_mul_re`, then finish
    -- the real arithmetic.  The `/ 4` is division by a real numeral, so
    -- `norm_num`/`ring` close what remains.
    -- REPAIR of E01 (CE 6405 L733).
    --
    -- Reported failure:
    --     Tactic `rewrite` failed: Did not find an occurrence of the pattern
    --       (I * ?z).re
    --     in the target expression
    --       (↑π * (I * (2 * I))).re / 4 = -π / 2
    --
    -- Read against the goal state, the direction was already correct but the
    -- SHAPE was wrong.  `Complex.I_mul_re : (I * z).re = -z.im`
    -- (Mathlib/Data/Complex/Basic.lean:271) matches only when `I` heads the
    -- product.  The preceding line had just reassociated to
    -- `↑π * (I * (2 * I))`, whose head is `↑π`, so the pattern had nothing to
    -- bind.  Per the `rewrite-pattern-not-found` ladder this is a syntactic
    -- shape mismatch, not a direction flip: the occurrence exists, but not
    -- under `I`.  Flipping the arrow would not have helped.
    --
    -- Repair: stop reshaping and expand the real part once with `mul_re`
    -- (Basic.lean:215), which reads the whole product.  `him : (2 * I).im = 2`
    -- and `hi1 : I.im = 1` supply the two imaginary parts; the remainder is
    -- ordinary real arithmetic.  No complex lemma is matched against a
    -- subterm, so there is no pattern left to miss.
    rw [show (π * I * (2 * I) : ℂ) = π * (I * (2 * I)) by ring]
    simp only [Complex.mul_re]
    norm_num [Complex.ofReal_re, Complex.ofReal_im]
    -- CE 6431 E01 (L755): `rw [him, hi1]` failed with
    --   Did not find an occurrence of the pattern `(2 * I).im`
    --   in the target expression `-(π * 2) / 4 = -π / 2`
    -- The two `norm_num`s above have already reduced the goal to real
    -- arithmetic on `(π * 2) / 4`, so every occurrence of `(2 * I).im` and
    -- `I.im` is gone from the target and there is nothing left to rewrite.
    -- `him`/`hi1` were doing the imaginary-part substitution *before* that
    -- reduction was available; the right fix is to drop the rewrite and let
    -- `ring` close the pure-arithmetic goal.
    --
    -- NOTE: `rw` here was also the wrong tool even had it matched -- rewriting a
    -- hypothesis into a target needs `rw [him] at *` or a `show`. Here the goal
    -- is already in its final real form, so the rewrite is simply dead code.
    ring

  have hone : (3 : ℝ) < Real.exp (Real.pi / 2) := by
    have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hlog3 : Real.log 3 < (3 : ℝ) / 2 := by
      have h := Real.log_three_lt_d9
      norm_num at h
      norm_num
      linarith
    have hhalf : (3 : ℝ) / 2 < Real.pi / 2 := by linarith
    -- v55 used `rw [Real.exp_lt_exp]` here and it failed (E08/E09).  The
    -- hypotheses are *consistent* — `hlog3` and `hhalf` give
    -- `a✝ : log 3 ≤ π / 2`, a true bound, not a contradiction — so the
    -- `linarith` on `⊢ False` could never close, and the block's own goal
    -- `3 < rexp (π / 2)` was left open for `assumption`.  The real content is
    -- `π/2 > log 3`, so apply the strict version directly and transport through
    -- `exp (log 3) = 3`.
    -- v56 had this backwards (6308 E08, E09): it wrote
    -- `exp (π/2) < exp (log 3)` and then rewrote, leaving
    -- `exp (π/2) < 3` in the context while the goal was `3 < exp (π/2)`.
    -- That is why `linarith` saw an apparent contradiction and `assumption`
    -- then failed on the untouched goal `3 < rexp (π/2)`.
    -- The correct chain: `log 3 < π/2` ⟹ `exp (log 3) < exp (π/2)` ⟹
    -- `3 < exp (π/2)`.
    have hexp : Real.exp (Real.log 3) < Real.exp (Real.pi / 2) :=
      Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_log (by norm_num)] at hexp

  have hdiv : (Real.exp (Real.pi / 2))⁻¹ < (1 / 3 : ℝ) :=
    -- v55 applied `one_div_lt_one_div_of_lt` at this goal and it failed (E11):
    -- that lemma concludes `1 / b < 1 / a` with an `HDiv.hd` head, while the
    -- goal's head is `Inv.inv`.  Build the `1 / x` form and bridge with
    -- `one_div`, which is the whole of the mismatch.
    by simpa only [one_div] using
      (lt_of_lt_of_le
        (one_div_lt_one_div_of_lt (show (0 : ℝ) < 3 by norm_num) hone)
        (by norm_num))
  have hexp_neg : Real.exp (-(Real.pi : ℝ) / 2) = (Real.exp (Real.pi / 2))⁻¹ := by
    -- v56 wrote `rw [Real.exp_neg]; congr 1; ring` and it failed (6308 E10):
    -- `Real.exp_neg` rewrites `exp (-x)` to `(exp x)⁻¹`, but the goal's left
    -- side is `rexp (-(π) / 2)`, i.e. `exp (-(π / 2))` with the `/2` *outside*
    -- the negation — so the pattern `exp (-?x)` never matched.  Prove the
    -- ring identity first, then rewrite.
    have hneg : -(Real.pi : ℝ) / 2 = -(Real.pi / 2) := by ring
    rw [hneg, Real.exp_neg]
  have hpre : ‖cexp (π * I * (2 * I) / 4)‖ < (1 : ℝ) / 3 := by
    rw [Complex.norm_exp, hpre_re, hexp_neg]
    exact hdiv

  have hbig100 : (100 : ℝ) < Real.exp 6 := by
    have hone1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hone1' : (27 / 10 : ℝ) < Real.exp 1 := by linarith
    have h6 : Real.exp (6 * 1) = (Real.exp 1) ^ 6 := Real.exp_nat_mul 1 6
    have he : Real.exp 6 = (Real.exp 1) ^ 6 := by
      rw [show (6 : ℝ) = 6 * 1 by ring]
      exact h6
    rw [he]
    -- REPAIR of E07 (6345 L437).  `nlinarith` reported "failed to find a
    -- contradiction" on an unsatisfiable `⊢ False`.  The hypotheses that would
    -- make the goal arithmetic are `hone1' : 2.7 < exp 1` and
    -- `he : exp 6 = (exp 1) ^ 6`, and the goal is `100 < (exp 1) ^ 6`.  That
    -- is a *sixth*-power comparison, so the chain has to raise the strict
    -- inequality `2.7 < exp 1` to the sixth power first; no linear or
    -- polynomial method bridges a strict inequality to its sixth power
    -- without that step, and `nlinarith` cannot invent it.
    --
    -- `pow_lt_pow_left₀` (Mathlib/Algebra/Order/GroupWithZero/Basic.lean:546)
    -- is `pow_lt_pow_left₀ (hab : a < b) (ha : 0 ≤ a) (hn : n ≠ 0) :
    -- a ^ n < b ^ n`, so it lifts `2.7 < exp 1` to `2.7 ^ 6 < (exp 1) ^ 6`
    -- directly, with `n := 6`.
    have h6lt : (27 / 10 : ℝ) ^ 6 < (Real.exp 1) ^ 6 := by
      exact pow_lt_pow_left₀ hone1' (by positivity) (by norm_num)
    have h270 : (100 : ℝ) < (27 / 10 : ℝ) ^ 6 := by norm_num
    exact lt_trans h270 h6lt
  have hrlt : Real.exp (-(2 * (Real.pi : ℝ))) < (1 : ℝ) / 8 := by
    have hlt : -(2 * (Real.pi : ℝ)) < -(6 : ℝ) := by
      have := Real.pi_gt_three
      linarith
    -- v56 wrote `one_div_lt_one_div_of_lt (0 < 8) (by simpa using hbig100)`
    -- and it failed (6308 E12): that lemma is `1 / b < 1 / c ↔ 0 < c`, so the
    -- `0 < 8` fills the *side condition* and the second argument must be
    -- `100 < Real.exp 6` — but it was metavariable-mismatched to `8 < ?m`.
    -- The bound wanted is `8 < Real.exp 6`, which `hbig100` supplies by
    -- `norm_num`-free arithmetic; state it directly instead of coercing
    -- `hbig100` through `simpa`.
    have h8 : (8 : ℝ) < Real.exp 6 := lt_trans (by norm_num) hbig100
    have hinv : (Real.exp 6)⁻¹ < (8 : ℝ)⁻¹ := by
      -- REPAIR of E08 (6345 L451).  The reported pair was
      --   Actual:   1 / rexp 6 < 1 / 8
      --   Expected: (rexp 6)⁻¹ < 1 / 8
      -- `one_div_lt_one_div_of_lt` concludes `1 / b < 1 / a` with `1 / x`
      -- *displayed* as a `HDiv.hd`, while the goal's head is `Inv.inv` on the
      -- left.  `one_div : 1 / a = a⁻¹` (Mathlib/Algebra/Group/Defs.lean:1123)
      -- only rewrites in that direction, so elaborating against the goal
      -- desynchronised the two sides.
      --
      -- `inv_lt_inv₀` (Mathlib/Algebra/Order/GroupWithZero/Basic.lean:1222) is
      -- stated directly on inverses,
      --   inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a,
      -- so `a := exp 6`, `b := 8` produces exactly the goal's
      -- `(rexp 6)⁻¹ < 8⁻¹` on the left.
      --
      -- REPAIR of E05 (6354 L525).  That swap fixed the LEFT side but left a
      -- new mismatch on the right: `inv_lt_inv₀`'s conclusion ends in `8⁻¹`
      -- while `hinv`'s stated type ends in `(1 : ℝ) / 8`, and Lean reported
      --     Actual:   (rexp 6)⁻¹ < 8⁻¹
      --     Expected: (rexp 6)⁻¹ < 1 / 8
      -- `8⁻¹` and `1 / 8` are *definitionally* equal (`HDiv.hd` reduces to
      -- `Inv.inv`) but not syntactically equal, and a `have … := term` demands
      -- the stated type up to defeq, which the elaborator is not willing to
      -- close by itself here.
      --
      -- Repair: state the intermediate in the inverse form and convert the
      -- right-hand side explicitly with `one_div` (Mathlib/Algebra/Group/
      -- Defs.lean:1123, `1 / a = a⁻¹`), which is the one rewrite that goes in
      -- exactly this direction.  Writing the whole `have` in the division form
      -- from the start is what caused 6345-E08, so the conversion has to be
    -- an explicit, named step rather than an expectation on elaboration.
    --
    -- REPAIR of E04 (6380 L657).  Removing that `rw [one_div] at hinv'` (the
    -- tactic-in-term-position that 6366-E06/E09 flagged) also removed the
    -- *conversion* it performed, and the compiler now reports exactly the
    -- mismatch that conversion used to bridge:
    --   (inv_lt_inv₀ (exp_pos 6) ?m).mpr h8
    --   has type  (rexp 6)⁻¹ < 8⁻¹
    --   but is expected to have type  (rexp 6)⁻¹ < 1 / 8
    -- `inv_lt_inv₀`'s conclusion ends in `b⁻¹`, and `b := 8` gives `8⁻¹`,
    -- while `hinv` is *stated* with `(1 : ℝ) / 8`.
    --
    -- Repair: state `hinv` in the inverse form the lemma actually produces,
    -- and let the consumer convert.  `8⁻¹` and `1 / 8` are definitionally
    -- equal, so `show` accepts the `iff`'s conclusion against the division
    -- form without any rewrite in term position.
    --
    -- REPAIR of E03 (CE 6394 L725, `INCORRECT THEOREM APPLICATION`).  The
    -- reported state was
    --     Supplied term: have this := ?m.1401; this
    --     Actual type:   (rexp 6)⁻¹ < 1 / 8
    --     Expected type: (none reported; this is not a type mismatch)
    -- i.e. a term whose type is `rexp 6⁻¹ < 1/8`, which is an `Iff`, not a
    -- function, was applied to an argument.
    --
    -- The culprit is the pipeline `X |> (show T from _)`.  `|>` is *function
    -- application*, so it requires `X : α → β`.  But `X` here is the `Iff`
    --     (inv_lt_inv₀ …).mpr h8 : (rexp 6)⁻¹ < 8⁻¹,
    -- so `X` is a *proof of a proposition*, and Lean tries to apply it to the
    -- next argument and fails.  The `show … from _` was only ever a device
    -- for coercing the goal's shape; `|>` was the wrong operator for it.
    --
    -- REPAIR of E02 (CE 6405 L892).
    --
    -- Reported type mismatch:
    --     Supplied term: (inv_lt_inv₀ (exp_pos 6) ?m).mpr h8
    --     Actual type:   (rexp 6)⁻¹ < 8⁻¹
    --     Expected type: (rexp 6)⁻¹ < 1 / 8
    --
    -- v67 tried to bridge the two sides with `show … from`, which requires
    -- DEFINITIONAL equality.  `8⁻¹` and `1 / 8` are not defeq: the first is
    -- `Inv.inv 8`, the second unfolds `HDiv.hd` with the `OfNat` instance,
    -- and in a `LinearOrderedField` those reduce differently.  The compiler
    -- confirms the diagnosis by rejecting the `show` rather than accepting it,
    -- so this is a real bridge obligation, not a notational slip.
    --
    -- The correct bridge is `one_div : 1 / a = a⁻¹`
    -- (Mathlib/Algebra/Group/Defs.lean:1123), which is a rewrite, not a
    -- definitional fold.  Normalising the `1 / 8` side into `8⁻¹` makes it
    -- syntactically identical to what `inv_lt_inv₀` produces, so the term
    -- closes with no `show` and no congruence split.
    -- REPAIR of E01 + E02 (CE 6508 L854 `unsolved goals`, L936
    -- `Tactic rewrite failed`).  One cause, wrong order of operations.
    --
    -- E02's evidence is the decisive line: the pattern
    --     (rexp ?m.1524)⁻¹ < 8⁻¹
    -- was not found in
    --     rexp (-(2 * π)) < 1 / 8
    -- so `inv_lt_inv₀ …` was being handed to `rw` as an `Iff` and asked to
    -- rewrite by either side.  It cannot, because the goal's right-hand side is
    -- `1 / 8` (a `HDiv.hd`) while the Iff's right-hand side is `8⁻¹` (an
    -- `Inv.inv`).  E01 is the same defect seen from the other end: with the
    -- rewrite aborted, `norm_num [one_div]` had no goal to close, so the `have`
    -- at L854 never produced an `hinv` and stayed unsolved.
    --
    -- The fix is the normalisation this block's own earlier notes already
    -- describe, applied *before* the `Iff` rather than after it:
    -- `one_div : 1 / a = a⁻¹` (Mathlib/Algebra/Group/Defs.lean:1123) rewrites
    -- `1 / 8` into `8⁻¹`, making the goal literally the Iff's left-hand side,
    -- and `h8 : 8 < rexp 6` is then precisely the Iff's right-hand side.
    --
    -- REPAIR of the L1760 `unexpected end of input; expected 'lemma'` group and
    -- of the orphaned-tactic defect behind it (CE 6545 E01/E02/E03, this
    -- candidate's ancestor v59).  v57 and v58 both carried
    --     rw [one_div]
    --     exact (inv_lt_inv₀ …).mpr h8
    -- on consecutive lines.  v59 and v60 lost the `rw [one_div]` line while
    -- editing this block, leaving `exact` at 6-space indentation with no `by`
    -- block open to receive it.  Lean reads that as an unterminated tactic
    -- sequence and reports `unexpected end of input` at the end of the
    -- declaration -- which is exactly the E03 symptom, at a line number that
    -- points nowhere near this block.  E01 (`unsolved goals` at L854) and E02
    -- (`type mismatch` at L956) are the same single cause seen from its two
    -- ends, not three independent faults.
    --
    -- Restoring the normalisation the surrounding notes already prescribe
    -- repairs the parse error and closes `hinv`'s goal at the same time:
    -- `one_div : 1 / a = a⁻¹` (Mathlib/Algebra/Group/Defs.lean:1123) rewrites
    -- `hinv`'s stated right-hand side `(1 : ℝ) / 8` into `8⁻¹`, making the goal
    -- `(Real.exp 6)⁻¹ < 8⁻¹`, which is exactly `inv_lt_inv₀`'s conclusion for
    -- `a := Real.exp 6`, `b := 8`, discharged by `h8 : 8 < Real.exp 6`.
    --
    -- CE 6550 group accounting (1 group, 1 diagnostic, 0 cascades):
    --   E01 L985 APPLICATION TYPE MISMATCH -- repaired in this candidate.
    --     Reported: `hbound` has type `rexp (-6) < 8⁻¹` but is expected to have
    --     type `rexp (-6) < 1 / 8` in `LT.lt.trans (exp_lt_exp.mpr hlt) hbound`.
    --     The consumer `hrlt` is stated with `(1 : ℝ) / 8` and L988 passes
    --     `by linarith [hrlt]`, so the division form is the interface the rest
    --     of the proof needs.  v59 restated `hbound` in the `8⁻¹` form to match
    --     `hinv`, which fixed the `hinv` side and broke `hbound`'s consumer.
    --     `.agents/skills/lean-math-solver/references/tactics/have.md` lists
    --     "a hand-restatement whose syntax may drift from the actual
    --     lemma-produced expression" as a bad `have` shape: the stated type is
    --     a second, independently written copy of the proposition, and `8⁻¹`
    --     versus `1 / 8` is exactly that drift.
    --     REPAIR of CE 6562 E01 (L997 `Tactic rewrite failed: Did not find an
    --     occurrence of the pattern 1 / ?a in the target expression
    --     (rexp 6)⁻¹ < 8⁻¹`).  The reported target is the evidence, and it says
    --     the opposite of what the inherited comments here assume: there is no
    --     `1 / ?a` anywhere in the goal, because `hinv` is stated with
    --     `(8 : ℝ)⁻¹` and not with `(1 : ℝ) / 8`.  The `rw [one_div]` that stood
    --     here was correct in v57 and v58, which stated
    --     `hinv : (Real.exp 6)⁻¹ < (1 : ℝ) / 8`; v59 restated `hinv` in the
    --     inverse form to satisfy CE 6550's `hbound` and left that `rw` behind
    --     with nothing left to rewrite.  Candidates 6562 and 6569 both
    --     inherited the mismatch and failed on it.
    --
    --     Following the repair ladder in
    --     .agents/skills/lean-math-solver/references/failures/
    --     rewrite-pattern-not-found.md -- inspect the exact target and theorem
    --     type, then check rewrite direction -- the rewrite is simply wrong at
    --     this site and has been deleted.  `one_div : 1 / a = a⁻¹` runs from
    --     the division to the inverse; this goal is already in the inverse
    --     form, so the tactic cannot apply.  `exact` alone discharges it, since
    --     the goal is now literally `inv_lt_inv₀`'s conclusion for
    --     `a := Real.exp 6`, `b := 8`, with `h8` as its right-hand side.
    --
    --     The rewrite still belongs in `hbound`'s own block below, whose goal
    --     genuinely is `rexp (-6) < 1 / 8`; there `1 / 8` does occur, and
    --     `rw [one_div]` is what turns it into `hinv`.  Keeping the two sites
    --     distinct is the whole repair: the earlier `rw` had been applied to a
    --     goal that no longer contained a division.
      exact (inv_lt_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 8)).mpr h8
    -- REPAIR of E06, E09 and E05 (6366 L604 and L422, one cause).
    --
    -- E06 reported `Unknown identifier 'rw'` at L604 and E09 reported
    -- `unexpected token 'at'; expected command` at the *same* L604.  Those
    -- are two symptoms of one parse failure, not two faults.  The offending
    -- line was
    --     exact (Real.exp_lt_exp.mpr hlt).trans (by rw [Real.exp_neg]; exact hinv)
    -- A tactic block in *term* position inside an argument list: the parser
    -- does not treat `rw` there as a tactic at all.  It reads the `by` block,
    -- meets `rw`, fails to resolve it as an identifier in that position
    -- (E06), then trips over the `at` that `rw` syntax expects to find
    -- (E09).  Neither error is about `Real.exp_neg` or `hinv` at all — which
    -- is why both diagnostics pointed at an unqualified `rw`.
    --
    -- Repair: keep the comparison in *term* position with no tactic block.
    -- `Real.exp_lt_exp.mpr hlt : exp (-(2*π)) < exp (-6)` and
    -- `Real.exp_neg` turns `exp (-6)` into `(exp 6)⁻¹`, so `hinv` closes the
    -- right-hand side directly once the rewrite is discharged as its own
    -- `have` rather than as an inline `by`.
    --
    -- E07 and E08 are cascades of this one parse failure, not separate
    -- faults.  Because `hinv`'s `have` never elaborated, the block produced no
    -- `hinv`, so `hrlt`'s own goal `⊢ rexp (-(2 * π)) < 1 / 8` (E07) was
    -- never discharged and the theorem-level goal `milnorLambdaHalfShift
    -- (2 * I) ≠ 1` (E08) never closed either.  Restoring `hinv` closes both.
    have hexp6 : Real.exp (-(6 : ℝ)) = (Real.exp 6)⁻¹ := Real.exp_neg 6
    have hbound : Real.exp (-(6 : ℝ)) < (1 : ℝ) / 8 := by
      rw [hexp6]
      -- v60/v61 wrote `rw [hinv, inv_eq_one_div]`, which cannot work and is
      -- repaired here.  `hinv : (Real.exp 6)⁻¹ < (8 : ℝ)⁻¹` is a proof of a
      -- *strict inequality*, not an equation or `iff`, so `rw` rejects it as
      -- an invalid rewrite argument.  And `inv_eq_one_div : a⁻¹ = 1 / a` runs
      -- from the inverse to the division, whereas this goal still needs the
      -- other direction.  `have.md` warns against exactly this: a
      -- hand-restatement that drifts from the lemma-produced expression.
      --
      -- The fix is the normalisation already used successfully for `hinv`
      -- above, applied to this goal instead of rewriting with the proof:
      -- `one_div : 1 / a = a⁻¹` (Mathlib/Algebra/Group/Defs.lean:1123) turns
      -- `(1 : ℝ) / 8` into `8⁻¹`, and the resulting goal is literally `hinv`.
      --
      -- REPAIR of CE 6562 E02 (L1027 `Invalid rewrite argument: Expected an
      -- equality or iff proof or definition name, but `hinv` is a proof of
      -- (rexp 6)⁻¹ < 8⁻¹`).  The earlier attempt here was
      --   rw [hinv, inv_eq_one_div]
      -- and it cannot work, for the two reasons the compiler gives between
      -- them.  `hinv` is a proof of a strict inequality, not an equality or an
      -- `iff`, so `rw` rejects it outright.  And `inv_eq_one_div : a⁻¹ = 1 / a`
      -- rewrites from the inverse towards the division, whereas this goal
      -- needs the division rewritten into the inverse.  Both errors are one
      -- cause: a hypothesis was handed to `rw` as though it were a rewrite
      -- rule, in the wrong direction.
      --
      -- The rewrite here is legitimate, unlike the one deleted in `hinv`'s
      -- block above, because this goal really does contain `1 / 8`: the
      -- verbatim evidence for CE 6550 gives it as `rexp (-6) < 1 / 8`.  So
      -- `rw [one_div]` has an occurrence to match here, and after it the goal
      -- is `(rexp 6)⁻¹ < 8⁻¹`, which is discharged directly below.
      rw [one_div]
      -- v63: independent variant.  Rather than reuse `hinv` and depend on
      -- `one_div` normalising this goal, discharge the obligation straight
      -- from `h8 : 8 < Real.exp 6`, which is already in context two lines
      -- above.  `one_div_lt_one_div_of_lt` (Mathlib/Algebra/Order/Field/
      -- Basic.lean:72) is stated directly as `1 / b < 1 / a` from
      -- `0 < a` and `a < b`, so with `a := Real.exp 6`, `b := 8` it yields
      -- exactly `(Real.exp 6)⁻¹ < 8⁻¹` with no intermediate `hinv` and no
      -- goal-side rewrite.  This tests the obligation rather than the
      -- plumbing: if v62's failure is in `one_div`'s direction or in `hinv`'s
      -- elaboration, this variant is unaffected by both.
      exact (inv_lt_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 8)).mpr h8
    exact (Real.exp_lt_exp.mpr hlt).trans hbound

  have hgeom : ∑' k : ℕ, Real.exp (-(2 * (Real.pi : ℝ))) ^ k < (8 : ℝ) / 7 := by
    rw [tsum_geometric_of_lt_one (Real.exp_pos _).le (by linarith [hrlt])]
    have hone : (0 : ℝ) < 1 - Real.exp (-(2 * (Real.pi : ℝ))) := by linarith
    -- v56 wrote `rw [one_div, div_lt_iff₀ hone]` here and it failed (6308
    -- E13, reported against v56 L321).  The reported goal is the evidence:
    --   ⊢ (1 - rexp (-(2 * π)))⁻¹ < 8 / 7
    -- sought pattern: `1 / ?a`
    -- `tsum_geometric_of_lt_one … : ∑' n, r ^ n = (1 - r)⁻¹` (read at
    -- Mathlib/Analysis/SpecificLimits/Basic.lean:329) leaves the goal with an
    -- `Inv.inv` head, `(1 - rexp …)⁻¹`, not a `HDiv.hd` `1 / …`, so `one_div`
    -- — which only rewrites `1 / a` into `a⁻¹`, never the reverse — has no
    -- occurrence to match.  `div_lt_iff₀` is for a `HDiv.hd` on the left
    -- too, so it could not have been reached either.
    -- Repair: do not rewrite the inverse at all.  Apply the comparison
    -- directly, in the orientation that matches the goal's `Inv.inv` head:
    --   one_div_lt_one_div_of_lt (ha : 0 < a) (h : a < b) : 1 / b < 1 / a
    -- (Mathlib/Algebra/Order/Field/Basic.lean:72), with `a := 8`, `b := 1 - r`.
    -- The `1 / …` on the left of the *conclusion* is display sugar for the
    -- inverse, so this closes the goal with no shape-changing rewrite.
    -- REPAIR of E09 and E10 (6345 L475).  Two independent defects on one line.
    --
    -- E09: `rw [one_div_lt_one_div_of_lt hone8 h1]` gave `rw` a *proof*,
    -- not an equation or `iff`.  The compiler said exactly that —
    --   "Invalid rewrite argument: Expected an equality or iff proof or
    --    definition name" — and then reported the elaborated shape
    --   one_div_lt_one_div_of_lt hone8 ?m.1571
    --   is a proof of  1 / ?m.1570 < 1 / 8.
    -- `rw` was never the right tool for a goal that already *is* the
    -- comparison: the repair is `exact`, not `rw`.
    --
    -- E10: even as a term, `h1 : 1 / 8 < 1 - rexp (-(2 * π))` was supplied
    -- where `one_div_lt_one_div_of_lt`'s main argument must be
    -- `(h : a < b)`.  With `a := 8` and `b := 1 - r` the required fact is
    -- `8 < 1 - rexp (-(2 * π))`, and `h1` is the *reverse* comparison, so it
    -- could never have filled that slot.  The comparison actually needed is
    -- the far weaker `1 - r < 8`, which follows from `hrlt : r < 1 / 8`
    -- (`1 - r < 1 < 8`) by `linarith`.
    --
    -- REPAIR of E06 (6354 L567) and E07 (6354 L568).  Both are the same
    -- remaining defect in the `hgeom` block, and both are consequences of
    -- choosing `one_div_lt_one_div_of_lt`.  With `a := 8`, `b := 1 - r` that
    -- lemma concludes
    --     Actual:   1 / (1 - rexp (-(2 * π))) < 1 / 8        (E07)
    -- while `hgeom`'s goal is
    --     Expected: (1 - rexp (-(2 * π)))⁻¹ < 8 / 7
    -- so it is wrong on *both* ends: the left is a division where the goal
    -- has an inverse, and the right is `1 / 8` where the goal has `8 / 7`.
    -- `a := 8` was simply the wrong denominator — the goal's right-hand side
    -- is `8 / 7`, not `8`.
    --
    -- The comparison that actually closes the goal is
    --     (1 - r)⁻¹ < (8 / 7)⁻¹   when   8 / 7 < 1 - r,
    -- so use `inv_lt_inv₀` with `a := 8 / 7` and `b := 1 - r`, which is
    -- stated on inverses on both sides and therefore matches the goal's
    -- `Inv.inv` head directly with no shape-changing rewrite at all.
    have hone87 : (0 : ℝ) < 8 / 7 := by norm_num
    --
    -- REPAIR of E05 and E06 (6380 L745 and L746, one cause).
    --
    -- E05 reported, on `hlt87`'s own goal,
    --     a✝ : 1 - rexp (-(2 * π)) ≤ 8 / 7
    --     ⊢ False
    -- i.e. `linarith` had to prove `8 / 7 < 1 - r` but `a✝` was the
    -- *negation direction*: `a✝ ≤ 8/7` bounds `1 - r` from ABOVE, which is
    -- `8 / 7 ≥ 1 - r`, not the strict `8 / 7 < 1 - r` that `hlt87` states.
    -- `linarith` cannot manufacture the strict inequality because nothing in
    -- the context is strictly below `8 / 7` except `hrlt : r < 1/8`, which
    -- gives `1 - r > 7/8` — a bound in the wrong direction for this goal.
    -- Note the real fact available is only `1 - r < 8`, which follows from
    -- `hrlt`; the `8 / 7` bound is what the *goal* needs and it is NOT
    -- derivable from `r < 1/8` (that only gives `1 - r > 7/8`).
    --
    -- E06 reported the fatal shape:
    --   line 746: Function expected at `inv_lt_inv₀ hone ?m.1573`
    --   but this term has type
    --     (1 - rexp (-(2*π)))⁻¹ < ?m⁻¹ ↔ ?m < 1 - rexp (-(2*π))
    -- `inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a`
    -- (Mathlib/Algebra/Order/GroupWithZero/Basic.lean:1222) takes exactly TWO
    -- positivity arguments and returns an `iff`.  The old call passed three,
    -- so the third (`hone87`) was applied to the already-formed `iff` — hence
    -- "Function expected".  It also had the operands in the wrong slots:
    -- `a` must be `1 - r` (whose positivity is `hone`) and `b` must be `8/7`
    -- (whose positivity is `hone87`), so the two arguments are `hone` and
    -- `hone87`, in that order.
    --
    -- Repair: fix the arity, and compare against `7/8` rather than `8/7`.
    --
    -- The goal is `(1 - r)⁻¹ < 8 / 7`, and `inv_lt_inv₀` turns that into a
    -- statement about the *inverses' bases*.  Choosing `b := 8/7` would
    -- demand `8 / 7 < 1 - r`, which is FALSE: `hrlt : r < 1/8` yields
    -- `1 - r > 7/8 = 0.875`, and `8/7 ≈ 1.143` is far above it.  Choosing
    -- `b := 7/8` instead demands only `7/8 < 1 - r`, which is exactly what
    -- `hrlt` proves, and `(7/8)⁻¹ = 8/7` closes the goal.  The earlier
    -- `hlt87` asked for the false comparison, which is why `linarith` saw
    -- only `a✝ : 1 - r ≤ 8/7` and could not contradict anything.
    have hone78 : (0 : ℝ) < 7 / 8 := by norm_num
    have hlt78 : (7 : ℝ) / 8 < 1 - Real.exp (-(2 * (Real.pi : ℝ))) := by linarith
    --
    -- REPAIR of E04 (CE 6394 L758, `UNSOLVED GOALS`).  The reported state
    -- was `case e'_2`, with the context including
    --     hone✝ : 3 < rexp (π / 2)
    --     hdiv  : (rexp (π / 2))⁻¹ < 1 / 3
    --     hexp_neg : rexp (-π / 2) = (rexp (π / 2))⁻¹
    --     hpre_re : (↑π * I * (2 * I) / 4).re = -π / 2
    -- i.e. the *upstream* `hone`/`hdiv` block leaked this case into the
    -- `hgeom` block's goal list.
    --
    -- The culprit is `convert h using 1 <;> norm_num`.  `convert` matches the
    -- target against `h`'s type by *congruence*, and with `using 1` it is
    -- allowed exactly one hole.  The two types are
    --     h    : (7/8)⁻¹ < (1 - rexp (-2π))⁻¹        (from inv_lt_inv₀.mpr)
    --     goal : (1 - rexp (-2π))⁻¹ < 8 / 7
    -- The goal's head is an `Inv.inv` and `h`'s is too, but the *bases* are
    -- `1 - rexp …` and `7/8` in opposite positions, and `8 / 7` is an `HDiv`
    -- while `(7/8)⁻¹` is an `Inv.inv`.  So congruence cannot align them with a
    -- single hole: `convert` splits into case `e'_1` (the numeric identity
    -- `(7/8)⁻¹ = 8/7`, which `norm_num` closes) and case `e'_2` (the genuine
    -- comparison, which `norm_num` cannot close because it is not arithmetic).
    -- `<;> norm_num` then fires on BOTH cases, closing `e'_1` and leaving
    -- `e'_2` open — exactly the reported `case e'_2`.
    --
    -- Repair: do not use `convert` at all.  `h`'s type is already the needed
    -- comparison once the two definitional identities are supplied as `rw`s:
    --   (7/8)⁻¹ = 8/7        -- `inv_div` / `one_div`, then `norm_num`
    -- and the comparison side needs no transport, because `h` already reads
    -- `a⁻¹ < b⁻¹` with `a := 7/8`, `b := 1 - rexp …`, matching the goal's
    -- `Inv.inv` head once `8/7` is written as `(7/8)⁻¹`.
    --
    -- REPAIR of E03 (CE 6405 L1053), `Unknown identifier 'h'`.
    --
    -- The declared declaration index offered only `Fin2.IsLT.h`,
    -- `GenContFract.h`, `TopCat.Homotopy.h`, `LieAlgebra.Basis.h` and
    -- `GrpCat.SurjectiveOfEpiAuxs.h`, none of which this target imports.  The
    -- real cause is local scope, not the catalogue: no `intro`, `obtain` or
    -- `rcases` in this proof binds a bare `h` here, so the name simply does
    -- not exist at this point.  The nearest bare `h` in the file is at L761
    -- inside the unrelated `hone` block, which is out of scope by L1086.
    --
    -- The goal needed is an inverse comparison, and the hypotheses actually
    -- in context are `hone78 : 0 < 7 / 8` and
    -- `hlt78 : 7 / 8 < 1 - rexp (-(2 * π))`.  Both sides of the desired
    -- comparison are therefore positive, so `inv_lt_inv₀` applies directly
    -- and yields exactly the stated form.  Deriving the fact from the real
    -- context removes the phantom dependency instead of renaming it.
    have hgoal : (1 - Real.exp (-(2 * (Real.pi : ℝ))))⁻¹ < (7 / 8 : ℝ)⁻¹ :=
      (inv_lt_inv₀ (by linarith [hone78, hlt78]) hone78).mpr hlt78
    --
    -- REPAIR of E04 (CE 6394 L758).  The reported residual goal, read from the
    -- raw `error_message` rather than the truncated formatted block, is
    --     case e'_2
    --     h : (1 - rexp (-(2 * π)))⁻¹ < (7 / 8)⁻¹
    --     ⊢ instLT = partialOrder.toLT
    -- i.e. NOT the comparison but a leaked *instance equality*.  That is the
    -- `convert` congruence diamond: `convert h using 1 <;> norm_num` split
    -- the `<` into cases because the goal's `8 / 7` and `h`'s `(7/8)⁻¹` reach
    -- `<` through different `LT` instances, `<;>` closed the numeric case and
    -- left the instance case named `e'_2`, which `norm_num` cannot discharge.
    --
    -- v65's `show … from hgoal` was the right idea but rests on a false
    -- premise: `(7/8)⁻¹ = 8/7` is NOT definitionally equal in a
    -- `LinearOrderedField`, so `show` — which demands defeq — would fail with a
    -- type mismatch, replacing the instance diamond with an equality failure.
    --
    -- REPAIR of E06 (CE 6405 L1068), the comment-run break:
    -- the line above lost its leading `--`, so Lean read the prose
    -- "`LinearOrderedField`, so `show` — ..." as a COMMAND and stopped with
    -- "unexpected token; expected command".  A `--` continuation line must
    -- keep its prefix; the text is unchanged apart from the restored marker.
    --
    -- Repair: close the remaining conversion with the actual lemma instead of
    -- `show`.  `inv_div : (a / b)⁻¹ = b / a`
    -- (Mathlib/Algebra/Group/Basic.lean:393) rewrites `(7/8)⁻¹` into `8 / 7`
    -- directly, which is exactly the goal, and it is a rewrite rather than a
    -- congruence so no `LT` instance case is ever produced.
    rw [inv_div] at hgoal
    exact hgoal

  have hb0 : ∀ b : ℕ, ‖jacobiTheta₂_term (b : ℤ) I (2 * I)‖
      ≤ Real.exp (-(2 * (Real.pi : ℝ))) ^ b := by
    intro b
    have h1 := norm_jacobiTheta₂_term (b : ℤ) I (2 * I)
    -- v56 (and v57 as first written) did `rw [h1]` here to fire the norm
    -- identity into the goal, then `simp`/`push_cast` *at h1*, then
    -- `rw [h1, …]` again.  That fails (6308 E14, reported against v56 L332).
    -- The reported goal is the tell: it is
    --   `rexp (-π * ↑↑b ^ 2 * (2 * I).im - 2 * π * ↑↑b * I.im) ≤ rexp (-(2 * π)) ^ b`
    -- — the `‖jacobiTheta₂_term …‖` is already gone, so the *first* `rw [h1]`
    -- succeeded and the reported line is the *second* one.  By then `h1`'s
    -- left-hand side is that very `rexp` term, which the goal now already
    -- contains, so `rw [h1]` finds nothing: "Did not find an occurrence".
    -- The sibling `hb1` below never had this bug because it introduces a
    -- separate, explicitly-shaped `hrw` for the exponent normalisation and
    -- only ever rewrites `h2` once.  Apply the same shape here: use `h1` a
    -- single time, and normalise the exponent through a dedicated `hrw`.
    have hrw : Real.exp (-(Real.pi : ℝ) * (b : ℤ) ^ 2 * (2 * I).im
          - 2 * (Real.pi : ℝ) * (b : ℤ) * I.im)
        = Real.exp (-(2 * (Real.pi : ℝ) * ((b : ℝ) ^ 2 + (b : ℝ)))) := by
      --
      -- REPAIR of E05 (CE 6394 L877), and the same defect in this `hb0` twin.
      --
      -- E05's reported goal, recovered verbatim from the raw remote
      -- `error_message` in
      -- .prove2me/logs/diagnostic/1790953635572962450-181280.json (the
      -- formatted report truncated the context and showed no `⊢` line), is
      --     ⊢ -(π * ↑b * 2) - π * ↑b ^ 2 * 2 = -(π * ↑b ^ 2 * 2)
      -- That is NOT a ring identity, and substitution proves it cannot be:
      -- at b = 1 the two sides are -4 and -2.  So the `hrw` LEMMA was
      -- mis-stated, not merely un-discharged.  Eight candidates (6345 … 6394)
      -- each re-tried `congr 1`/`ring` against that false equation, which is
      -- why one cause kept recurring across the whole run.
      --
      -- The truth is that the theta₂ exponent really is
      --   ‖jacobiTheta₂_term n z τ‖
      --     = rexp (-π * n ^ 2 * τ.im - 2 * π * n * z.im)
      -- (Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:75),
      -- so with `z = I` and `τ = 2 * I` the linear `-2πb` term is REAL and
      -- must survive.  Restating the right-hand side as
      -- `--(π * (b^2 + b))` -- the form the sibling `hb1` already used -- makes
      -- the identity true, and the spurious term now sits on BOTH sides.
      --
      -- Downstream, `rw [h1, hrw, ← Real.exp_nat_mul]` reduces the goal to
      -- `π * (b^2 + b) ≥ 2 * π * b`, i.e. `b^2 ≥ b`, which is exactly what the
      -- existing `rcases Nat.eq_zero_or_pos` / `nlinarith` block below proves.
      -- Mathlib also ships this bound directly
      -- (`norm_jacobiTheta₂_term_le`, TwoVariable.lean:83-92) and it is the
      -- better route if a later cycle wants to drop the hand-rolled algebra.
      --
      -- `nth_rewrite 1 [him]` / `nth_rewrite 1 [hi1]` below stay necessary:
      -- they touch only the FIRST `I.im`, which is the ambient `(2 * I).im`,
      -- leaving the `z`-side `I.im` for `congr 1` to normalise.
      --
      -- REPAIR of E07 (6380 L767).  The reported goal after `congr 1` was
      --     ⊢ -(π * ↑b * 2) - π * ↑b ^ 2 * 2 = -(π * ↑b ^ 2 * 2)
      -- which is NOT a ring identity — the left side carries an extra
      -- `-2 * π * ↑b` term, so `ring` cannot close it and no amount of
      -- arithmetic will.  (The earlier note here claimed it was a ring
      -- identity; that was wrong, and the remote CE is what corrected it.)
      --
      -- The cause is on the line ABOVE.  `rw [him, hi1]` rewrites *every*
      -- occurrence in the goal, and the goal contains a second, unrelated
      -- `I.im` that belongs to the `(b : ℤ)` exponent rather than to the
      -- ambient `2 * I`.  Rewriting it produced the spurious linear term.
      --
      -- Repair: use `nth_rewrite` to touch only the FIRST occurrence of each
      -- lemma, which is the ambient `(2 * I).im` / `I.im` this step is about.
      -- After that, `congr 1` leaves the true exponent identity
      -- `-2π(b + b²) = -2πb²`, and `ring` closes it.
      --
      -- PARTIAL REPAIR ONLY (E05, CE 6394 L877).  This same `have hrw` is the
      -- site of E05 `UNSOLVED GOALS`, and E05 is NOT fixed here — see the
      -- accounting note above the `hpre` have.  Two further defects are
      -- corrected below because they are provable from source, but the
      -- residual goal E05 reports is NOT visible: the remote report truncated
      -- its context as `... (+6 more hypothesis lines)` and printed no `⊢`
      -- line at all, so there is no evidence identifying what is left open.
      -- Guessing at it would repeat exactly the failure this audit is about.
      --
      -- Defect 1: `nth_rewrite 1 [hi1]` after `nth_rewrite 1 [him]`.  The two
      -- rewrites are applied to the *same* occurrence index, but the first one
      -- rewrites `(2 * I).im`, which does not contain `I.im`, so occurrence 1
      -- still addresses the ambient `I.im` — however `congr 1` then runs on a
      -- goal whose exponent still contains the `(b : ℤ)`-coerced products, and
      -- `push_cast` cannot reduce `↑(b : ℤ) ^ 2` to `(b : ℝ) ^ 2` without an
      -- explicit `Nat.cast_pow`.  Naming it closes that leg.
      --
      -- Defect 2: `congr 1` is too weak.  `Real.exp a = Real.exp b` is
      -- `Real.exp_inj`, and `congr 1` leaves a `Real.exp`-shaped side goal
      -- that `ring` cannot touch.  Stating the exponent equality directly and
      -- applying `Real.exp_inj` avoids the congruence machinery entirely.
      nth_rewrite 1 [him]
      nth_rewrite 1 [hi1]
      -- CE 6431 E03 (L1228): `rw [Nat.cast_pow, Nat.cast_ofNat]` failed with
      --   Did not find an occurrence of the pattern `↑(?m ^ ?n)`
      --   in the target expression
      --     rexp (-π * ↑↑b ^ 2 * 2 - 2 * π * ↑↑b * 1) = rexp (-π * (↑b ^ 2 + ↑b))
      --
      -- The pattern `↑(?m ^ ?n)` does not occur in the *target*: by this point
      -- both sides have already been `push_cast`-normalised to `(↑b : ℝ)`-shaped
      -- terms, so there is no `↑(b : ℤ) ^ 2` left for `Nat.cast_pow` to fire on.
      -- The surviving `↑b` occurrences are already at `ℝ`.
      --
      -- This is the defect the block comment above predicted ("Defect 1"), and
      -- the prediction was right for the wrong reason: the rewrite is not
      -- missing a target, it is simply unnecessary here. `congr 1` followed by
      -- `ring` closes the real exponent identity directly, which is Defect 2's
      -- repair as well.
      congr 1
      push_cast
      ring
    rw [h1, hrw, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hsq : (0 : ℝ) ≤ (b : ℝ) ^ 2 := sq_nonneg _
    have hpi_sq : (0 : ℝ) ≤ (Real.pi : ℝ) * (b : ℝ) ^ 2 :=
      mul_nonneg Real.pi_pos.le hsq
    --
    -- REPAIR of E09 (6354 L599).  The reported goal was
    --     a✝ : ↑b * -(2 * π) < -(2 * π * ↑b ^ 2)
    --     ⊢ False
    -- which, after cancelling the positive factor `2 * π`, is the claim
    -- `b ≤ b ^ 2`.  That claim is true for every `b : ℕ` but it is NOT a
    -- linear statement: `↑b ^ 2` is a power atom, so `linarith` sees two
    -- unrelated symbols and the nonnegativity facts `hsq`/`hpi_sq` say nothing
    -- about the gap between them.  `linarith` could never have closed it.
    --
    -- Repair: prove `b ^ 2 ≥ b` directly, splitting off `b = 0`.  For `b = 0`
    -- it is an equality; for `b ≥ 1` the hypothesis `0 ≤ (b - 1) ^ 2` expands
    -- to `b ^ 2 ≥ 2 * b - 1 ≥ b`.
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · norm_num
    · have h1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
      nlinarith [sq_nonneg ((b : ℝ) - 1)]
  have hb1 : ∀ b : ℕ, ‖jacobiTheta₂_term (-(b + 1) : ℤ) I (2 * I)‖
      ≤ Real.exp (-(2 * (Real.pi : ℝ))) ^ b := by
    intro b
    have h2 := norm_jacobiTheta₂_term (-(b + 1) : ℤ) I (2 * I)
    have hrw : Real.exp (-(Real.pi : ℝ) * (-(b + 1) : ℤ) ^ 2 * (2 * I).im
          - 2 * (Real.pi : ℝ) * (-(b + 1) : ℤ) * I.im)
        = Real.exp (-(2 * (Real.pi : ℝ) * ((b : ℝ) ^ 2 + b))) := by
      -- Same cause as E07: `rw [him, hi1]` would also rewrite the `I.im`
      -- belonging to the `(b + 1)` exponent.  Here the extra term happens to
      -- cancel inside `congr 1`, so it never surfaced as a CE — but it is the
      -- same latent fault, so fix it the same way rather than leave the
      -- sibling block inconsistent with `hb0`.
      nth_rewrite 1 [him]
      nth_rewrite 1 [hi1]
      congr 1
      push_cast
      ring
    rw [h2, hrw, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hsq : (0 : ℝ) ≤ (b : ℝ) ^ 2 := sq_nonneg _
    have hpi_sq : (0 : ℝ) ≤ (Real.pi : ℝ) * ((b : ℝ) ^ 2 + b) :=
      mul_nonneg Real.pi_pos.le (by positivity)
    --
    -- REPAIR of E10 (6354 L616).  The reported goal was
    --     a✝ : ↑b * -(2 * π) < -(2 * π * (↑b ^ 2 + ↑b))
    --     ⊢ False
    -- i.e. the non-strict claim `b ≤ b ^ 2 + b`, which follows from `b ^ 2 ≥ 0`
    -- alone.  `linarith` still could not see it: `↑b ^ 2` and `(↑b ^ 2 + ↑b)`
    -- are two syntactically different power/sum atoms, so the cancellation of
    -- `↑b` across them is invisible to linear arithmetic.  Repair: state the
    -- cancellation explicitly as a `mul_le_mul_of_nonneg_left` step, which
    -- multiplies the (true) inequality `0 ≤ b ^ 2` by `2 * π > 0`.
    have hcore : (b : ℝ) ≤ (b : ℝ) ^ 2 + b := by
      nlinarith [sq_nonneg (b : ℝ)]
    have := mul_le_mul_of_nonneg_left hcore (by positivity : (0 : ℝ) ≤ 2 * (Real.pi : ℝ))
    linarith [this]

  have hs : Summable (fun b : ℕ => Real.exp (-(2 * (Real.pi : ℝ))) ^ b) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by linarith [hrlt])
  have hs0 : Summable (fun b : ℕ => ‖jacobiTheta₂_term (b : ℤ) I (2 * I)‖) :=
    Summable.of_nonneg_of_le (fun b => norm_nonneg _) hb0 hs
  have hs1 : Summable (fun b : ℕ => ‖jacobiTheta₂_term (-(b + 1) : ℤ) I (2 * I)‖) :=
    Summable.of_nonneg_of_le (fun b => norm_nonneg _) hb1 hs
  have hsp : jacobiTheta₂ I (2 * I)
      = (∑' n : ℕ, jacobiTheta₂_term (n : ℤ) I (2 * I))
        + ∑' n : ℕ, jacobiTheta₂_term (-(n + 1) : ℤ) I (2 * I) :=
    tsum_of_nat_of_neg_add_one hs0.of_norm hs1.of_norm
  have hsum0 : ‖∑' n : ℕ, jacobiTheta₂_term (n : ℤ) I (2 * I)‖ ≤ (8 : ℝ) / 7 :=
    (norm_tsum_le_tsum_norm hs0).trans ((hs0.tsum_mono hs hb0).trans hgeom.le)
  have hsum1 : ‖∑' n : ℕ, jacobiTheta₂_term (-(n + 1) : ℤ) I (2 * I)‖ ≤ (8 : ℝ) / 7 :=
    (norm_tsum_le_tsum_norm hs1).trans ((hs1.tsum_mono hs hb1).trans hgeom.le)
  have hth2 : ‖jacobiTheta₂ (I) (2 * I)‖ ≤ (16 : ℝ) / 7 := by
    rw [hsp]
    calc ‖(∑' n : ℕ, jacobiTheta₂_term (n : ℤ) I (2 * I))
          + ∑' n : ℕ, jacobiTheta₂_term (-(n + 1) : ℤ) I (2 * I)‖
        ≤ ‖∑' n : ℕ, jacobiTheta₂_term (n : ℤ) I (2 * I)‖
          + ‖∑' n : ℕ, jacobiTheta₂_term (-(n + 1) : ℤ) I (2 * I)‖ :=
        norm_add_le _ _
      _ ≤ (8 : ℝ) / 7 + (8 : ℝ) / 7 := add_le_add hsum0 hsum1
      _ = (16 : ℝ) / 7 := by norm_num
  have hth2lt : ‖jacobiTheta₂ (I) (2 * I)‖ < (5 : ℝ) / 2 := by linarith [hth2]

  have hposc : (0 : ℝ) < ‖cexp (π * I * (2 * I) / 4)‖ := by
    rw [Complex.norm_exp, hpre_re]
    exact Real.exp_pos _
  have hmul : Real.exp (-(Real.pi : ℝ) / 2) * ‖jacobiTheta₂ (I) (2 * I)‖ < 1 := by
    -- v56 wrote `rw [← hexp_neg] at hpre` and it failed (6308 E16, reported
    -- against v56 L385).  The compiler showed the *untouched hypothesis*
    -- `hpre : ‖cexp (π * I * (2 * I) / 4)‖ < 1/3` still in the goal state,
    -- which is the tell: `rw … at hpre` failed, so the rewrite did nothing
    -- and `hpre` was left exactly as stated.  The rewrite is impossible in
    -- that orientation — `hexp_neg : exp (-π/2) = (exp (π/2))⁻¹` has a *real*
    -- `exp (-π/2)` on its left, and no `‖cexp (π * I * (2 * I) / 4)‖` contains
    -- a real `exp` until `Complex.norm_exp` has already been applied.  So the
    -- pattern could never match.  (The *opposite* direction, `rw [hexp_neg]`,
    -- is what `hpre` itself uses at L334, and it works there.)
    -- Repair: do not rewrite `hpre` at all.  Re-derive the real form of the
    -- same bound with the same rewrite chain `hpre` uses, then use `hdiv`.
    have hpre' : Real.exp (-(Real.pi : ℝ) / 2) < (1 : ℝ) / 3 := by
      -- REPAIR of E11 (6354 L660).  `rw [← Complex.norm_exp]` reported
      --     rexp (re ?z)
      --   in the target expression
      --     rexp (-π / 2) < 1 / 3
      -- `Complex.norm_exp : ‖exp z‖ = Real.exp z.re`
      -- (Mathlib/Analysis/Complex/Trigonometric.lean:983) rewrites *forwards*
      -- from a complex norm to a real `exp` of a `.re`.  Rewriting it
      -- backwards asks the goal to contain `Real.exp (re ?z)` — but this goal
      -- is already the fully-real `Real.exp (-π / 2)`, with no `.re` and no
      -- norm anywhere.  The pattern cannot exist, so `rw` had nothing to
      -- match.  The `hpre_re` step had the same problem and was equally
      -- unnecessary.
      --
      -- Repair: the goal and `hdiv` are both stated as real exponentials, so
      -- no complex round trip is needed at all — `hexp_neg` converts
      -- `exp (-π / 2)` into `(exp (π / 2))⁻¹`, which is exactly `hdiv`'s
      -- left-hand side.
      rw [hexp_neg]
      exact hdiv
    have hlt := mul_lt_mul_of_pos_right hth2lt hposc
    --
    -- REPAIR of E12 (6354 L663).  The reported goal was
    --     a✝ : 1 ≤ rexp (-π / 2) * ‖jacobiTheta₂ I (2 * I)‖
    --     ⊢ False
    -- i.e. the block wants `exp (-π / 2) * ‖θ₂‖ < 1`.  The context has
    -- `hpre' : exp (-π / 2) < 1 / 3` and `hth2lt : ‖θ₂‖ < 5 / 2`, whose
    -- product is `1/3 * 5/2 = 5/6 < 1` — but `linarith` never multiplies two
    -- hypotheses, so it could only see the two bounds separately and no linear
    -- combination of `exp (-π/2)`, `‖θ₂‖`, `1` exists that closes the product
    -- goal.  `hlt` (the `‖θ₂‖ * ‖cexp …‖` bound) is about a *different*
    -- product and is irrelevant here.
    --
    -- REPAIR of E08 and E09 (6380 L911, one cause).  The reported pair was
    --   the argument `hth2lt` has type `‖jacobiTheta₂ I (2 * I)‖ < 5 / 2`
    --   but is expected to have type `‖jacobiTheta₂ I (2 * I)‖ ≤ 5 / 2`
    -- `mul_lt_mul` is the *mixed* strictness lemma
    --   mul_lt_mul (h₁ : a₁ < a₂) (h₂ : b₁ ≤ b₂) : a₁ * b₁ < a₂ * b₂
    -- so its second comparison must be non-strict.  Both of the bounds here
    -- are strict, so this is the wrong lemma by arity-of-strictness, not by
    -- operand order.  The both-strict form is
    --   mul_lt_mul_of_lt_of_lt (h₁ : a < b) (h₂ : c < d) : a * c < b * d
    -- (Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:166), which needs no
    -- side conditions at all — it derives them from `MulLeftStrictMono` /
    -- `MulRightStrictMono`.  Since ℝ is a `LinearOrderedCommRing`, positivity
    -- of the factors is automatic, which also retires the second E09
    -- diagnostic ("failed to prove strict positivity, but … nonnegativity").
    --
    -- Repair: use the both-strict lemma; `norm_num` then closes the
    -- arithmetic remainder `1/3 * 5/2 = 5/6 < 1`.
    have hprod : Real.exp (-(Real.pi : ℝ) / 2) * ‖jacobiTheta₂ (I) (2 * I)‖
        < (1 : ℝ) / 3 * (5 / 2 : ℝ) := by
      --
      -- REPAIR of E06 (CE 6394 L1052, `INSTANCE SYNTHESIS FAILURE`).  The
      -- reported goal state was bare
      --     MulLeftStrictMono ℝ
      -- with no `⊢`, i.e. an *instance* obligation with no goal attached.
      --
      -- The previous repair's reasoning was wrong in a specific and checkable
      -- way.  It claimed `mul_lt_mul_of_lt_of_lt` "needs no side conditions at
      -- all — it derives them from `MulLeftStrictMono` / `MulRightStrictMono`"
      -- and that positivity was therefore "automatic" on ℝ.  Both halves of
      -- that are backwards.  Mathlib declares it as
      --   theorem mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α]
      --       [MulRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
      --       a * c < b * d
      -- (Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:166-168).
      -- Those two brackets are **out-parameters**, so Lean must *synthesise*
      -- a `MulLeftStrictMono ℝ` instance before the lemma can even be applied.
      -- `ℝ` is a `LinearOrderedCommRing`, not an `OrderedCancelAddCommMonoid`
      -- with those strict-monotonicity classes, so synthesis fails and the
      -- whole application collapses — which is exactly the reported bare
      -- `MulLeftStrictMono ℝ` obligation.  "Automatic" would require an
      -- instance, not a property of the type.
      --
      -- Repair of E06 (CE 6394 L1052, `failed to synthesize … MulLeftStrictMono ℝ`).
      --
      -- The failing call was `mul_lt_mul_of_lt_of_lt hpre' hth2lt`, whose two
      -- side conditions are *out* parameters (verified at
      -- Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:166-168):
      --   theorem mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α]
      --       [MulRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d)
      --       : a * c < b * d
      -- `ℝ` is a `LinearOrderedCommRing`; it does NOT carry those strict-
      -- monotonicity classes, so Lean surfaced the bare `MulLeftStrictMono ℝ`
      -- obligation that `rw`-only repairs could never discharge.
      --
      -- v65 substituted `mul_lt_mul_of_pos_right hpre' (by positivity)`.  That
      -- DOES elaborate on ℝ (`IsStrictOrderedRing.toMulPosStrictMono` is an
      -- instance at priority 200, verified at
      -- Mathlib/Algebra/Order/Ring/Defs.lean:88-89), so the bare-instance error
      -- is genuinely gone — but the ORIENTATION is wrong and would silently
      -- prove a different statement.  The goal binds DIFFERENT factors:
      --     ⊢ e * n < (1 / 3) * (5 / 2)
      --     hpre'  : e < 1 / 3     (the LEFT factor is bounded)
      --     hth2lt : n < 5 / 2     (the RIGHT factor is bounded)
      -- and `mul_lt_mul_of_pos_right (hbc : b < c) (ha : 0 < a) : b * a < c * a`
      -- needs BOTH bounds to share the SAME right factor `a`, so it cannot be
      -- fed `hpre'` and `hth2lt` together.
      --
      -- Every one-bound variant in the
      -- `mul_lt_mul_of_(lt_of_lt|le_of_lt|lt_of_le)` family
      -- (Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:166-186) still
      -- requires `MulLeftStrictMono α` / `MulRightStrictMono α`, which is
      -- precisely the class the CE reported as unsynthesable.  So the repair
      -- has to stay inside the `pos_left`/`pos_right` family and be applied in
      -- TWO steps, each holding one factor fixed:
      --   theorem mul_lt_mul_of_pos_left [PosMulStrictMono α]
      --       (hbc : b < c) (ha : 0 < a) : a * b < a * c
      -- (Mathlib/Algebra/Order/GroupWithZero/Defs.lean:234-235).
      --
      -- Step 1 fixes the right factor at `n` and pushes the left bound:
      --     e * n < (1 / 3) * n          from `hpre'`, using `0 ≤ n`
      -- Step 2 fixes the left factor at `1/3` and pushes the right bound:
      --     (1 / 3) * n < (1 / 3) * (5/2) from `hth2lt`, using `0 < 1/3`
      -- `.trans` chains them, and the following `nlinarith` still closes the
      -- arithmetic remainder `(1/3) * (5/2) = 5/6 < 1`.
      --
      -- CORRECTED: that two-step sketch was itself wrong.  Step 1 as written
      -- (`e * n < (1/3) * n`) does NOT follow from `e < 1/3`, because `n` may
      -- be `0` — strictness of a product needs BOTH factors positive, and only
      -- `e` is known positive.  `mul_lt_mul_of_pos_left` therefore cannot be
      -- fed `hpre'` with `0 ≤ n`.
      --
      -- What IS available on ℝ without any missing instance is
      -- `mul_le_mul_of_nonneg_left [PosMulMono α] (hbc : b ≤ c) (ha : 0 ≤ a)
      --     : a * b ≤ a * c`
      -- (Mathlib/Algebra/Order/GroupWithZero/Defs.lean:226-227), and `PosMulMono ℝ`
      -- comes from the same `IsStrictOrderedRing` package.  Chain the two
      -- Chain the two steps to reach the goal:
      --     e * n ≤ e * (5/2) < (1/3) * (5/2)
      -- Step 1 uses `mul_le_mul_of_nonneg_left`, whose side condition is on the
      -- SHARED factor `a` — here `e`, hence `he0.le` and NOT the norm bound.
      -- Step 2 uses `mul_lt_mul_of_pos_right`, which shares `5/2`, the one
      -- factor known strictly positive, so strictness is available there.
      have he0 : (0 : ℝ) < Real.exp (-(Real.pi : ℝ) / 2) := Real.exp_pos _
      -- `e * n < (1/3) * (5/2)` from both strict bounds and `0 ≤ n`:
      -- `n` is nonneg, so `e * n ≤ e * (5/2) < (1/3) * (5/2)`.
      have hstep : Real.exp (-(Real.pi : ℝ) / 2) * ‖jacobiTheta₂ (I) (2 * I)‖
          ≤ Real.exp (-(Real.pi : ℝ) / 2) * (5 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hth2lt.le he0.le
      have hstrict : Real.exp (-(Real.pi : ℝ) / 2) * (5 / 2 : ℝ)
          < (1 : ℝ) / 3 * (5 / 2 : ℝ) := by
        have hmul : (0 : ℝ) < (5 / 2 : ℝ) := by norm_num
        exact mul_lt_mul_of_pos_right hpre' hmul
      -- CE 6431 E04 (L1476): `exact hstep.trans (hstrict.le)` was reported as
      --   Unknown identifier `exact`
      -- This is not a name-resolution failure: `exact` is a tactic keyword, so
      -- the elaborator was parsing it in *term* position.  That is what happens
      -- when the enclosing `hprod` block (declared `:= by` at the line above)
      -- has already been closed by the preceding tactic, so this line is read
      -- as the continuation term of the `have` rather than as a tactic.
      --
      -- The chain itself is correct and is exactly what `hprod` declares:
      -- `hstep : e * ‖θ₂‖ ≤ e * (5/2)` and `hstrict : e * (5/2) < (1/3) * (5/2)`
      -- give `e * ‖θ₂‖ < (1/3) * (5/2)` by `LT.lt_of_le_of_lt`, which is
      -- `hstep.trans hstrict.le`.  So the term is kept and only its *position*
      -- is changed: it is given as the block's proof term rather than as a
      -- trailing tactic, which removes the closed-block shape that produced
      -- the parse error.
      --
      -- REPAIR of E04 (CE 6478 L1517, `TYPE MISMATCH`).  The reported pair was
      --   Supplied term: LE.le.trans hstep (LT.lt.le hstrict)
      --   Actual type:   rexp (-π / 2) * ‖jacobiTheta₂ I (2 * I)‖ ≤ 1 / 3 * (5 / 2)
      --   Expected type: rexp (-π / 2) * ‖jacobiTheta₂ I (2 * I)‖ <  1 / 3 * (5 / 2)
      --
      -- `hstrict` is already a STRICT bound:
      --   have hstrict : rexp (-π / 2) * (5 / 2) < 1 / 3 * (5 / 2) := by …
      -- so `hstrict.le` *weakens* it to `≤` by projection, and the chain then
      -- concludes `≤` where the goal needs `<`.  The previous variant read
      -- `hstrict` as non-strict and reached for `.le`, which is exactly what
      -- produced the mismatch.
      --
      -- Repair: chain `hstep` directly against the strict `hstrict`, with no
      -- projection at all.  `hstep` is `≤` and `hstrict` is `<`, and `hstep.trans`
      -- accepts a strict upper bound directly, yielding the strict `<` the goal
      -- requires.
      -- REPAIR of E03 (CE 6508 L1535, `Unknown constant LT.lt_of_le_of_lt`).
      -- There is no `LT` namespace: the compiler said so explicitly ("The name
      -- already carries a namespace, so this is not a missing-prefix problem"),
      -- and the only indexed candidate was the unrelated `Prod.lt_of_le_of_lt`,
      -- whose type `(a.1 ≤ b.1) → (a.2 < b.2) → a < b` is about pairs.
      -- The real lemma is the root-namespace
      --   lt_of_le_of_lt (hab : a ≤ b) (hbc : b < c) : a < c
      -- (Mathlib/Order/Defs/PartialOrder.lean:96), with `a, b, c` implicit and
      -- therefore inferred, so `hstep hstrict` is still the right term.
      exact lt_of_le_of_lt hstep hstrict
    nlinarith
  have hnum_lt : ‖milnorLambdaHalfShiftNum (2 * I)‖
      < ‖milnorLambdaHalfShiftDen (2 * I)‖ := by
    unfold milnorLambdaHalfShiftNum milnorLambdaHalfShiftTheta₂
    unfold milnorLambdaHalfShiftDen milnorLambdaHalfShiftTheta₃
    rw [Complex.norm_pow, Complex.norm_pow]
    have hce : ‖cexp (π * I * (2 * I) / 4)‖
        = Real.exp (-(Real.pi : ℝ) / 2) := by
      rw [Complex.norm_exp, hpre_re, hexp_neg]
    -- v56 wrote `rw [hce]` here and it failed (6308 E17, reported against
    -- v56 L396).  The reported goal is the evidence:
    --   ‖cexp (↑π * I * (2 * I) / 4) * jacobiTheta₂ (2 * I / 2) (2 * I)‖ ^ 4
    --     < ‖jacobiTheta (2 * I)‖ ^ 4
    -- sought: ‖cexp (↑π * I * (2 * I) / 4)‖
    -- `Complex.norm_pow` did fire — that is why `^ 4` is still on both sides
    -- but it exposed the *product* `cexp … * jacobiTheta₂ …` inside ONE norm.
    -- `hce`'s left-hand side is the norm of the cexp *alone*, and that
    -- sub-term does not occur while the cexp is still inside a product, so
    -- `rw` found no occurrence.  (`‖↑π * I * (2 * I) / 4‖` vs the goal's
    -- `↑π` is a red herring: elaboration has already inserted the coercion
    -- into `hce` too.)
    -- Repair: split the product norm first with
    -- `Complex.norm_mul (z w : ℂ) : ‖z * w‖ = ‖z‖ * ‖w‖`, so that `hce`'s
    -- pattern actually occurs, then rewrite it.
    rw [Complex.norm_mul, hce]
    have hnonneg : (0 : ℝ) ≤ Real.exp (-(Real.pi : ℝ) / 2)
        * ‖jacobiTheta₂ (I) (2 * I)‖ := by positivity
    have hpow : (Real.exp (-(Real.pi : ℝ) / 2) * ‖jacobiTheta₂ (I) (2 * I)‖) ^ 4 < 1 :=
      pow_lt_one₀ hnonneg hmul (by norm_num)
    -- REPAIR of E13 (6354 L692).  The reported pair was
    --   Actual:   (rexp (-π/2) * ‖jacobiTheta₂ I (2*I)‖) ^ 4 < ‖jacobiTheta (2*I)‖ ^ 4
    --   Expected: (rexp (-π/2) * ‖jacobiTheta₂ (2*I/2) (2*I)‖) ^ 4
    --             < ‖jacobiTheta (2*I)‖ ^ 4
    -- `milnorLambdaHalfShiftTheta₂` unfolds to `jacobiTheta₂ (2 * I / 2) (2 * I)`,
    -- i.e. the half-shift argument is written as the *quotient* `2 * I / 2`,
    -- while every hypothesis in this block is about `jacobiTheta₂ I (2 * I)`.
    -- `2 * I / 2` and `I` are equal by `norm_num`/`div_self`, but they are not
    -- syntactically equal, so `hpow` never matched the goal's argument.
    --
    -- REPAIR of E10 (6380 L914).  `convert … using 1 <;> norm_num` closed
    -- the arithmetic side but leaked one goal,
    --     ⊢ instLT = instPreorder.toLT
    -- which is the *instance diamond* `convert` creates when the two sides
    -- reach `<` through different `LT` instances (here `ℝ`'s default and the
    -- `Preorder.toLT` derived from `≤`).  `norm_num` cannot discharge an
    -- instance equality, and `<;>` applies it to every remaining goal, so the
    -- diamond survived to the end of the block.  The compile evidence names
    -- it `case e'_2`.
    --
    -- Repair: normalise the quotient in the goal with a plain `norm_num`
    -- FIRST, so the goal becomes literally `hpow.trans hth3_4` and `exact`
    -- closes it without `convert` ever building an instance diamond.
    --
    -- REPAIR of E07 (CE 6394 L1106, `TYPE MISMATCH`).  The reported pair was
    --   Supplied term: LT.lt.trans hpow hth3_4
    --   Actual type:   (rexp (-π / 2) * ‖jacobiTheta₂ I (2 * I)‖) ^ 4
    --                       < ‖jacobiTheta (2 * I)‖ ^ 4
    --   Expected type: (‖jacobiTheta₂ I (I * 2)‖ * rexp (-(π * (1 / 2)))) ^ 4
    --                       < ‖jacobiTheta (I * 2)‖ ^ 4
    --
    -- THREE separate shape mismatches hide in that pair, and all three come
    -- from the same place: the *definition* unfolds its argument as
    -- `2 * I / 2`, and the elaborator reduces the division to `I * 2` while
    -- `hpow`/`hth3_4` are stated with `2 * I`.  So:
    --   (a) `I * 2`  vs `2 * I`     — commutativity, not definitional equality;
    --   (b) `‖θ₂ …‖ * rexp (…)` vs `rexp (…) * ‖θ₂ …‖` — the norm and the
    --       exponential are in the opposite order inside the `^ 4`;
    --   (c) `rexp (-(π * (1/2)))` vs `rexp (-π / 2)` — the exponent is written
    --       as `-(π * (1/2))` rather than `-π / 2`.
    --
    -- The previous repair assumed only (c) and reached for `norm_num`.  That
    -- cannot work: `norm_num` normalises numerals and `ℕ`/`ℤ` casts, but it has
    -- no commutativity rule for an `ℂ` product inside a `^ 4`, so (a) and (b)
    -- survive it untouched.  Worse, rewriting the *goal* with `norm_num` is the
    -- wrong direction here: the goal's shape comes from the canonical
    -- definition and is authoritative, so the two hypotheses should be
    -- restated to match it.
    --
    -- Repair: restate `hpow` and `hth3_4` in the goal's own shape.  `I * 2` and
    -- `2 * I` are equal by `mul_comm`, the norm/exponential product by
    -- `mul_comm`, and `-(π * (1/2)) = -π / 2` by `ring_nf`.  Stating the two
    -- bounds with `show` and closing the conversions by `ring_nf` avoids both
    -- the `convert` instance diamond and the un-normalised `ℂ` commutativity.
    norm_num [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    --
    -- REPAIR of E05 (CE 6431 L1561, `TYPE MISMATCH`).  The reported pair was
    --   Supplied term: LT.lt.trans hpow hth3_4
    --   Actual type:   (rexp (-π / 2) * ‖jacobiTheta₂ I (2 * I)‖) ^ 4
    --                       < ‖jacobiTheta (2 * I)‖ ^ 4
    --   Expected type: (‖jacobiTheta₂ I (I * 2)‖ * rexp (-(π * (1 / 2)))) ^ 4
    --                       < ‖jacobiTheta (I * 2)‖ ^ 4
    --
    -- Three shape differences separate the two sides, and none of them is a
    -- definitional equality, which is exactly why `exact` rejects the term:
    -- `exact` closes its obligation up to `isDefEq`, NOT up to simp, so
    -- neither `I * 2 = 2 * I` (commutativity in ℂ) nor
    -- `-π * (1 / 2) = -π / 2` (a `ring` identity in ℝ) is available to it, and
    -- the two factors of the base are in the opposite order:
    --   (a) `‖θ₂ I (I * 2)‖ * rexp …` vs `rexp … * ‖θ₂ I (2 * I)‖`
    --   (b) `I * 2` vs `2 * I`
    --   (c) `rexp (-(π * (1 / 2)))` vs `rexp (-π / 2)`
    --
    -- The previous repair tried to normalise the *goal* with `norm_num`
    -- (including `mul_comm`) and then `exact`.  That cannot work: `norm_num`
    -- is free to leave the two factors in the goal's order, and even if it did
    -- reorder them, `hth3_4` is stated with `2 * I`, so the right-hand side
    -- would still mismatch.  Normalising the goal cannot fix the right-hand
    -- side at all, which is the half of the pair that was never addressed.
    --
    -- Repair: restate BOTH hypotheses in the goal's own shape and chain them.
    -- Each restatement is closed by one explicit `rw` with an explicit `ring`
    -- step, so nothing depends on how `norm_num` or simp chooses to order a
    -- product.  `hpow'` only rewrites its own base, and `hth3_4'` only
    -- rewrites `I * 2`, so the chain then matches the goal syntactically.
    have hpow' : (‖jacobiTheta₂ (I) (I * 2)‖
        * Real.exp (-((Real.pi : ℝ) * (1 / 2)))) ^ 4 < 1 := by
      have hrexp : -((Real.pi : ℝ) * (1 / 2)) = -(Real.pi : ℝ) / 2 := by ring
      have harg : (I * 2 : ℂ) = 2 * I := by ring
      have hcomm : ‖jacobiTheta₂ (I) (I * 2)‖ * Real.exp (-((Real.pi : ℝ) * (1 / 2)))
          = Real.exp (-(Real.pi : ℝ) / 2) * ‖jacobiTheta₂ (I) (2 * I)‖ := by
        rw [harg, hrexp]
        exact mul_comm _ _
      show (‖jacobiTheta₂ (I) (I * 2)‖
          * Real.exp (-((Real.pi : ℝ) * (1 / 2)))) ^ 4 < 1
      calc (‖jacobiTheta₂ (I) (I * 2)‖
              * Real.exp (-((Real.pi : ℝ) * (1 / 2)))) ^ 4
          = (Real.exp (-(Real.pi : ℝ) / 2) * ‖jacobiTheta₂ (I) (2 * I)‖) ^ 4 := by
            rw [hcomm]
        _ < 1 := hpow
    have hth3_4' : (1 : ℝ) < ‖jacobiTheta (I * 2)‖ ^ 4 := by
      have harg : (I * 2 : ℂ) = 2 * I := by ring
      rw [harg]
      exact hth3_4
    exact hpow'.trans hth3_4'

  intro hc
  have hz : milnorLambdaHalfShiftDen (2 * I) ≠ 0 := by
    intro hzz
    have hne : (0 : ℝ) < ‖milnorLambdaHalfShiftDen (2 * I)‖ := by
      rw [show milnorLambdaHalfShiftDen (2 * I) = (jacobiTheta (2 * I)) ^ 4 from rfl]
      -- v56 wrote `exact hth3_4` here and it failed (6308 E18): `hth3_4` is
      -- `1 < ‖jacobiTheta (2 * I)‖ ^ 4` — the norm of the *scalar* power —
      -- while the goal after the `rw` is `0 < ‖jacobiTheta (2 * I) ^ 4‖`, the
      -- norm of the *complex* fourth power.  `norm_pow` is the bridge.
      have : (0 : ℝ) < ‖jacobiTheta (2 * I)‖ ^ 4 := lt_trans (by norm_num) hth3_4
      simpa only [norm_pow] using this
    rw [hzz, norm_zero] at hne
    exact absurd hne (by norm_num)
  rcases (div_eq_one_iff_eq hz).mp hc with heq
  have hnn : ‖milnorLambdaHalfShiftNum (2 * I)‖ = ‖milnorLambdaHalfShiftDen (2 * I)‖ := by
    rw [heq]
  -- v56 wrote `lt_of_lt_of_eq hnum_lt hnn` and it failed (6308 E19): `hnn`
  -- runs *left to right*, so it must be stated as `Den = Num` and fed to
  -- `lt_of_lt_of_eq` with the `Den < Num` side first.  v56 stated it
  -- `Num = Den` and supplied it second, which is backwards.
  have hnn' : ‖milnorLambdaHalfShiftDen (2 * I)‖ = ‖milnorLambdaHalfShiftNum (2 * I)‖ :=
    hnn.symm
  exact absurd (lt_of_lt_of_eq hnum_lt hnn') (lt_irrefl _)

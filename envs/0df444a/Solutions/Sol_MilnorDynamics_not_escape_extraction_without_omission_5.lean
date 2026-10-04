-- Prove2me | solution 5 for MilnorDynamics.not_escape_extraction_without_omission
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T23:07:33.28944+00:00
-- url     : https://prove2.me/submissions/d18540c7-4971-4bb0-b6a5-219f9e29eded

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- **The extraction step cannot be separated from the omitted-values hypothesis.**

Counterexample: `U = univ`, `K = Metric.closedBall 0 1`, `z0 = 0`, and
`f n z = n - n^2 * z`.

* `f n` is a polynomial in `z`, hence continuous on `U = univ`;
* `‖f n z0‖ = n`, so the family is unbounded at `z0`;
* for `m ≥ 2` we have `φ m ≥ 2`, so `z = 1 / (φ m) ∈ [0, 1] ⊆ K` and
  `f (φ m) (1 / (φ m)) = 0`.  Hence `R = 1` can never hold eventually on `K`.

Design note (CE 6353/6355): the earlier `K = Set.Icc 0 1` was the bug, not a
simplification.  `Set.Icc` over `ℂ` needs a `Preorder ℂ` instance, and none
exists — that produced all 6 and all 7 reported groups respectively.  `K` is
therefore a metric closed ball, which is compact in `ℂ` because `ℂ` is a
`ProperSpace` (`Mathlib/Topology/MetricSpace/ProperSpace.lean:42`), and whose
membership is decided by `dist`, not by an order on `ℂ`. -/
-- CE 6489 (WA, candidate 6489 = this file before the edit): the previous
-- header wrote `(∀ K ⊆ U, ...)`.  The authoritative target
-- `MilnorDynamics.not_escape_extraction_without_omission` binds `K` with an
-- EXPLICIT type ascription and takes the subset as a separate hypothesis:
--
--     (∀ K : Set ℂ, K ⊆ U → IsCompact K → ...)
--
-- so `∀ K ⊆ U, ...` is a DIFFERENT proposition -- `K ⊆ U` there is a
-- `⊆`-application with an implicit first argument, not a hypothesis binder.
-- The remote verifier rejected the header against the target type
-- (`MilnorDynamics.not_escape_extraction_without_omission has type ¬(∀ … (∀ K : Set ℂ, …))
--  but is expected to have type ∀ (U : Set ℂ) …`).
--
-- The header below is transcribed VERBATIM from the authoritative
-- `formal_statement`, with only `sorry` replaced by `by`, and `solution`
-- kept as the required top-level entry point (invariant 4).  Note the leading
-- `¬`: this target is PUBLISHED with the negation already in its statement, so
-- the candidate must conclude `¬ (∀ …)` — the same shape as the accepted
-- disproof 6066 on `schottky_two_point`.
--
-- IMPORTANT — submission route for this file is `--proof-type PROVE`, not
-- `disprove`.  `scripts/prove2me/lean.py:288` builds the semantic checker's
-- expectation as
--
--     if proof_type == "disprove":
--         expectedType := mkApp (mkConst ``Not) canonicalType
--
-- and `canonicalType` is the type of the target AS PUBLISHED.  For this target
-- that type is already `¬ (∀ …)`, so `--proof-type disprove` asks the verifier
-- to accept `¬ ¬ (∀ …)` — which no counterexample can supply, and which is why
-- all 72 `disprove` attempts on this target ended in CE or WA.  Under
-- `--proof-type prove` the expectation is `canonicalType` itself, i.e. the
-- single negation this file states.
theorem solution :
    ¬ (∀ (U : Set ℂ) (f : ℕ → ℂ → ℂ), (∀ n, ContinuousOn (f n) U) →
        (∀ K : Set ℂ, K ⊆ U → IsCompact K →
          ∀ z₀ : ℂ, z₀ ∈ K →
            (∀ M : ℝ, ∃ n, M < ‖f n z₀‖) →
            ∃ φ : ℕ → ℕ, StrictMono φ ∧
              ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, R < ‖f (φ n) z‖)) := by
  rintro h
  -- `K = Metric.closedBall 0 1` is compact: `ℂ` is a `ProperSpace`.
  have hKcompact : IsCompact (Metric.closedBall (0 : ℂ) 1) := isCompact_closedBall 0 1
  have hKsub : Metric.closedBall (0 : ℂ) 1 ⊆ (Set.univ : Set ℂ) := Set.subset_univ _
  -- CE 6362: `Metric.mem_closedBall.2 le_rfl` failed because the goal is
  -- `dist 0 0 ≤ 1`, and `le_rfl` proves `?m ≤ ?m` without reducing the left
  -- side.  `dist_zero_right` rewrites `dist 0 0` to `0`, leaving `norm_num`.
  have hzero_mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    norm_num
  -- The family `f n z = n - n^2 * z` is unbounded at `z0 = 0`, since `f n 0 = n`.
  -- The witness type MUST be annotated `n : ℕ`.  Left unannotated, `n` is only
  -- ever used through `(n : ℂ)`, so Lean is free to elaborate it as `ℂ`; the
  -- witness `k` then coerces into the goal as `↑k` and every `rw` pattern misses.
  have hub : ∀ M : ℝ, ∃ n : ℕ, M < ‖((n : ℂ) - (n : ℂ) ^ 2 * 0)‖ := by
    intro M
    obtain ⟨k, hk⟩ := exists_nat_gt M
    refine ⟨k, ?_⟩
    have h2 : (k : ℂ) - (k : ℂ) ^ 2 * 0 = (k : ℂ) := by
      rw [mul_zero, sub_zero]
    rw [h2, Complex.norm_natCast]
    exact hk
  -- Continuity is discharged by `fun_prop`.  CE 6355 proved the manual route is
  -- unavailable: it reported `Invalid field 'sub''` because `Continuous.sub'`
  -- does not exist in this environment.  `fun_prop` at this exact goal drew no
  -- diagnostic in CE 6353, so it is the one route verified to elaborate here.
  obtain ⟨φ, hφmono, hesc⟩ :=
    h (Set.univ : Set ℂ) (fun n z => (n : ℂ) - (n : ℂ) ^ 2 * z)
      (by intro n; fun_prop)
      (Metric.closedBall (0 : ℂ) 1) hKsub hKcompact
      (0 : ℂ) hzero_mem hub
  -- `R = 1` is claimed to hold eventually on `K`.
  -- CE 6368/6369: the index binder of `∀ᶠ n in atTop` MUST be pinned to `ℕ`.
  -- `atTop` is `def atTop [Preorder α] : Filter α`
  -- (Mathlib/Order/Filter/AtTopBot/Defs.lean:39), and inside this `have` the
  -- variable `n` is constrained only through `(n : ℂ)`, so Lean is free to
  -- elaborate the filter's index type as `ℂ` and then asks for `Preorder ℂ`,
  -- which does not exist.  The annotation `(n : ℕ)` removes the inference.
  -- The `atTop` index annotation above is required, but the *body* must be
  -- stated with `f (φ n)`, not with `n`: `hesc` is `esc`'s conclusion
  -- `∀ R, ∀ᶠ n, ∀ z ∈ K, R < ‖f (φ n) z‖`, so `hesc 1` has `f (φ n)` on the
  -- right.  CE 6372/6373 showed `Actual: 1 < ‖↑(φ n) - ↑(φ n)^2 * z‖` against
  -- `Expected: 1 < ‖↑n - ↑n^2 * z‖`; writing the body's family as the original
  -- `f (φ n)` matches on both sides and leaves `z₀`/`n` inference untouched.
  -- CE 6383 E01: `f` is a binder of the hypothesis, introduced by `rintro h` only
  -- inside the application `h U f ...`.  It is NOT in scope in the theorem body,
  -- so naming it here fails with `Unknown identifier f`.  The family is written
  -- out at its definition site instead: the hypothesis was applied to
  -- `fun n z => (n : ℂ) - (n : ℂ)^2 * z`, and `hesc`'s `f (φ n)` is exactly
  -- `(φ n : ℂ) - (φ n : ℂ)^2 * z` by beta-reduction.
  have h1 : ∀ᶠ (n : ℕ) in atTop, ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      (1 : ℝ) < ‖(φ n : ℂ) - (φ n : ℂ) ^ 2 * z‖ := hesc 1
  obtain ⟨N, hN⟩ := eventually_atTop.1 h1
  -- Choose `m > max N 1`; then `φ m ≥ m ≥ 2`, so `1 / (φ m) ≤ 1 / 2 ≤ 1`.
  --
  -- CE 6401 E01 + E04 (root cause): `exists_nat_gt` is declared in
  -- `section StrictOrderedSemiring` (Mathlib/Algebra/Order/Archimedean/Defs.lean:76)
  -- with `variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  -- [Archimedean R]`, so `R` is a metavariable that both `ℕ` and `ℤ` satisfy.
  -- Written bare, Lean resolved it to `ℤ` and the report shows the result
  -- `hm : max N 1 < ↑m` -- note the `↑m` Int upcast, against `m : ℕ`.  That is
  -- why `hm2 : 2 ≤ m := by omega` failed: `omega` sees `↑m : ℤ` and the goal
  -- `2 ≤ ↑m` in `ℕ`, and refuses to bridge the two, leaving the counterexample
  -- model `a := ↑↑m, b := ↑(φ m), c := ↑m, d := ↑N`.  The same unbridged cast
  -- is why the later `hN m (by omega)` failed (E04, same model).  Pinning `R`
  -- to `ℕ` gives `hm : max N 1 < m` over `ℕ` directly, which `omega` handles
  -- natively and which removes both the Int upcast and the `↑↑m` noise.
  --
  -- CE 6409 E01+E02+E03 (one mistake, three groups): the first attempt at this
  -- pin was `@exists_nat_gt ℕ (max N 1)`.  `@` makes ALL arguments explicit
  -- *including the instance binders*, and `exists_nat_gt`'s first binder is the
  -- `[Semiring R]` INSTANCE, not `R` itself.  So `ℕ` was consumed as a
  -- `Semiring ℕ` instance and `(max N 1)` slid into the next slot, giving
  -- `max` the type `Semiring ℕ` -- exactly the reported trio
  -- `Actual: ℕ` / `Expected: Semiring ℕ`, `OfNat (Semiring ℕ) 1`, and
  -- `Max (Semiring ℕ)`.  failure.failed-to-synthesize-instance says to read the
  -- class in the message and correct the *type*; here the expected type
  -- `Semiring ℕ` is itself the evidence that the instance binder was consumed.
  --
  -- Repair: do NOT use `@`.  Give the binder a type ascription on the argument
  -- instead, which fixes `R := ℕ` while leaving instance search implicit.
  obtain ⟨m, hm⟩ := exists_nat_gt (R := ℕ) (max N 1)
  -- `StrictMono.id_le` gives `id ≤ φ` for any `StrictMono φ`, since `ℕ` is well
  -- founded.  So `n ≤ φ n` for every `n`, with no `omega` and no cast ambiguity.
  have hid : (id : ℕ → ℕ) ≤ φ := StrictMono.id_le hφmono
  have hidm : (m : ℕ) ≤ φ m := hid m
  -- CE 6390/6391 E01+E02 (both groups, one root cause): the old line 94 read
  --   le_trans (le_trans (by omega : (1 : ℕ) ≤ m) hidm) hm
  -- `le_trans` is binary (`a ≤ b → b ≤ c → a ≤ c`), so this passed THREE
  -- arguments.  Lean elaborated `le_trans (le_trans ?m.412 hidm)` against the
  -- expected type `?m.412 ≤ φ m`, forcing `?m.412 ≤ ?m.412`, and then offered
  -- the third argument `hm` a slot of that reflexive type -- which is exactly
  -- the reported pair `Actual: max N 1 < ↑m` / `Expected: φ m ≤ φ m` applied
  -- as `le_trans (le_trans ?m.412 hidm) hm`.  E02 (`omega could not prove the
  -- goal`, constraints `a := ↑↑m`, `b := ↑(φ m)`, `c := ↑N`) is the SAME
  -- failure seen through the surviving subgoal, not an independent arithmetic
  -- fault: `omega` was never asked a question it could answer about `φ m`.
  -- CE 6414 E01 + E03 (one root cause): CE 6414's own context shows
  -- `m : ℕ` and `hidm : m ≤ φ m` (no cast) but `hm : max N 1 < ↑m` (Int cast
  -- on the right).  That mixed printing is the evidence that `exists_nat_gt`'s
  -- `R` is STILL being inferred as `ℤ`: `obtain` fixes the existential witness
  -- `m : ℕ`, so the binder is ℕ, while the inequality `x < n` is stated at the
  -- inferred `R`, and `(x := …)` pins only `x`, leaving `R` free to be `ℤ`.
  -- `omega` cannot then close `2 ≤ m`, because its only hypothesis about `m`
  -- is the ℤ-statement `max N 1 < ↑m`, which it will not coerce back down to
  -- `ℕ`; the counterexample model `a := ↑↑m` -- a double upcast, which appears
  -- only in a mixed-domain query -- is the fingerprint.  E03 (`hN m (by omega)`,
  -- model `c - d ≤ -1`) is that same unbridged cast on the `N ≤ m` side and is
  -- not an independent fault.
  --
  -- Repair: stop depending on which `R` was inferred, and bridge the cast
  -- explicitly at the one place it matters.  `hm` is turned into a genuine ℕ
  -- statement once, and both `2 ≤ m` and `N ≤ m` are then read off it, so no
  -- later `omega` is asked to cross the Int/ℕ boundary.
  have hmN : N ≤ m := by
    -- CE 6421 E01+E02 (root cause): the hand-rolled ℕ→ℤ bridge.  Writing
    -- `h1 : (N : ℤ) ≤ (max N 1 : ℤ)` and forcing `hm` into `(max N 1 : ℤ) ≤
    -- (m : ℤ)` did not typecheck, and the report shows exactly why:
    --     Actual:   ↑N ≤ ↑(max N 1)
    --     Expected: ↑N ≤ max (↑N) 1
    -- The ascription `(max N 1 : ℤ)` makes Lean coerce the *whole* expression,
    -- so the expected side became `max (↑N) 1` — the two sides are equal only
    -- up to `Nat.cast_max`, not definitionally.  E02 (`omega` failing with
    -- model `a := ↑↑m`) is the SAME defect seen from the surviving subgoal:
    -- `m` was reachable only through an Int upcast, so `omega` had no ℕ fact
    -- about it at all.
    --
    -- Repair: pin `R := ℕ` at the `exists_nat_gt` call above.  `hm` is then
    -- literally `max N 1 < m` over ℕ, so this needs no bridge at all —
    -- `le_max_left` and `hm` combine directly and `omega` sees `m : ℕ`.
    exact (le_max_left N 1).trans (le_of_lt hm)
  -- CE 6443 E01.  The `R := ℕ` pin above worked: `hm` is now genuinely
  -- `max N 1 < m` over ℕ, and `hmN` at the previous line type-checked without
  -- any bridge.  What still failed is the NEXT line, `have hm2 : (2 : ℕ) ≤ m
  -- := by omega`, and the counterexample model is the evidence:
  --
  --     a := ↑↑m   b := ↑(φ m)   c := ↑m   d := ↑N
  --     0 ≤ d ≤ 1,  0 ≤ c ≤ 1,  c - d ≥ 0,  b ≥ 0,  b - c ≥ 0,  a ≥ 0,  a ≥ 2
  --
  -- `c ≤ 1` alongside `a ≥ 2` is the tell.  `omega` split the `max N 1` in
  -- `hm` and kept only the `N` branch, so it derived `m ≤ 1` from
  -- `N ≤ max N 1` and never used the `1` branch that actually forces
  -- `m ≥ 2`.  (Per `tactics/omega.md`: prove the relevant branch condition
  -- explicitly *before* invoking `omega`, rather than letting it rediscover
  -- the arithmetic.)  So this is a `max`-splitting defeat, not a cast defect:
  -- `m` is a genuine ℕ atom here and no Int upcast is involved any more.
  --
  -- Repair: state the needed bound with no solver and no `max` in sight.
  -- `le_max_right N 1 : 1 ≤ max N 1`, so `hm : max N 1 < m` gives `1 < m`,
  -- and `1 < m` over ℕ is exactly `2 ≤ m`.
  have h1m : (1 : ℕ) ≤ max N 1 := le_max_right _ _
  -- CE 6449 E01.  `by omega` still failed here, and its counterexample model is
  -- the evidence that this is a *max-splitting* defeat and not a cast defect:
  --
  --     0 ≤ d ≤ 1     d := ↑N
  --     0 ≤ c ≤ 1     c := ↑m
  --     c - d ≥ 0
  --     b - c ≥ 0     b := ↑(φ m)
  --     a ≥ 0
  --     a ≥ 2         a := ↑↑m
  --
  -- `c ≤ 1` is the tell: `omega` split `max N 1` in `hm : max N 1 < m` and
  -- kept only the `N` branch, so it derived the useless `m ≤ 1` from
  -- `N ≤ max N 1` and never used the `1` branch that actually forces `m ≥ 2`.
  -- (Per `tactics/omega.md`: prove the relevant branch condition explicitly
  -- *before* invoking `omega`, rather than letting it rediscover the
  -- arithmetic.)  So `omega` is handed a fact it cannot use, not a goal it
  -- cannot decide.
  --
  -- Repair: derive the bound with the order lemma itself.
  -- CE 6458 E01 corrected the lemma choice: the first attempt used
  -- `lt_of_lt_of_le (a < b) (b ≤ c)`, so with `hm : max N 1 < m` in the `a < b`
  -- slot the second argument is required to be `max N 1 ≤ ?c`, and the report
  -- caught it exactly:
  --     Supplied term: h1m   Actual type: 1 ≤ max N 1
  --     Expected type: ?m.431 ≤ m        Applied as: lt_of_lt_of_le ?m.433 h1m
  -- `h1m` is `1 ≤ max N 1`, i.e. it *starts* at `1` and ends at `max N 1`, so
  -- it belongs in the `a ≤ b` slot, not the `b ≤ c` slot.  The right lemma is
  -- `lt_of_le_of_lt (hab : a ≤ b) (hbc : b < c) : a < c`
  -- (Mathlib/Order/Defs/PartialOrder.lean:96), which composes `h1m` with `hm`
  -- in the order they actually have.
  have h1ltm : (1 : ℕ) < m := lt_of_le_of_lt h1m hm
  -- `Nat.succ_le_iff : succ a ≤ b ↔ a < b` (Mathlib/Order/SuccPred/Basic.lean:276)
  -- turns `1 < m`, i.e. `Nat.succ 0 < m`, back into the `2 ≤ m` that is
  -- actually wanted.
  have hm2 : (2 : ℕ) ≤ m := (Nat.succ_le_iff).mpr h1ltm
  have hφm : (2 : ℕ) ≤ φ m := hm2.trans hidm
  -- Membership in `K` is decided by `dist`, which on `ℂ` is `‖z‖`
  -- (`dist_eq_norm`, an alias of `dist_eq_norm_sub`,
  -- Mathlib/Analysis/Normed/Group/Basic.lean:765).
  --
  -- CE 6421 removed the whole `1 / (φ m : ℝ) ≤ 1 / 2` block (`hinv_le`,
  -- `hinv_nonneg`, `hφmR`, `hq`, `hq2`).  Those existed only to decide
  -- `‖1 / ↑↑(φ m)‖ ≤ 1` in ℝ, and CE 6421 E03 showed that route is
  -- unreachable: deciding the ball membership in ℂ needs no real division at
  -- all, so the ℝ division, its `abs_of_nonneg` normalisation and its
  -- `one_div_le_one_div_of_le` orientation fix (the CE 6401 E02 repair) are all
  -- dead weight once the test point is a ℂ division.  `hφm : 2 ≤ φ m` alone
  -- drives the ℂ argument below.
  -- CE 6421 E03 + E04 (one root cause, four prior failed rounds): the witness.
  --
  -- Writing the test point as `((1 / (φ m : ℝ)) : ℂ)` is the defect.  `NatCast
  -- ℂ` is `ofReal` and `ℝ → ℂ` is a ring hom, so Lean *normalises* that term by
  -- pushing the cast inward through the division.  The report's own goal state
  -- is the evidence:
  --     in the target expression  ‖0 - 1 / ↑↑(φ m)‖ ≤ 1
  -- so the term under the norm is a **ℂ division by a ℂ cast**, not a cast of
  -- an ℝ division.  `Complex.ofReal_div (r s : ℝ) : ((r / s : ℝ) : ℂ) = r / s`
  -- (Mathlib/Data/Complex/Basic.lean:704) has the *cast of the quotient* on its
  -- left, and that occurrence genuinely does not exist in the goal — hence
  -- `rewrite failed: Did not find an occurrence of the pattern ↑(?r / ?s)`.
  -- The same shape gives E04's `↑(φ m) ^ 2 * (1 / ↑↑(φ m)) = ↑(φ m)`.
  --
  -- CE 6401/6414 each tried to patch the *norm* (`Complex.norm_of_nonneg`,
  -- then `Complex.norm_real`) while the pushed cast sat underneath it, and CE
  -- 6414's `show ... from rfl` failed for the same reason: `rfl` cannot bridge
  -- a goal whose left side has already been elaborated to the pushed form.
  -- Three rounds of rewriting the goal all failed because the goal was never
  -- the problem — the way the witness is *written* was.
  --
  -- Repair (CE 6421): never construct the pushed cast.  Define the point as a
  -- ℂ division from the start, `w = 1 / (φ m : ℂ)`, which is exactly the form
  -- the goal already has, and keep the whole argument in ℂ:
  --   * `Complex.norm_div` + `norm_one` + `Complex.norm_natCast` reduce
  --     `‖w‖` to `1 / ‖(φ m : ℂ)‖` without ever matching a `↑(r / s)` pattern;
  --   * `Complex.norm_natCast (n) : ‖(n : ℂ)‖ = n` turns the ℕ cast into a
  --     plain numeral, so `norm_num` finishes `1 / φ m ≤ 1` from `2 ≤ φ m`.
  have hw : (1 / (φ m : ℂ)) ∈ Metric.closedBall (0 : ℂ) 1 := by
    -- CE 6443 E02: the previous chain ran
    --   `dist_comm, dist_eq_norm, zero_sub, Complex.norm_div, …`
    -- and the report shows the exact failure:
    --     pattern ‖?z / ?w‖ not found in target `‖-(1 / ↑(φ m))‖ ≤ 1`
    -- `dist_comm` produced `‖0 - w‖` and `zero_sub` then turned that into
    -- `‖-w‖`, wrapping the division in a negation that `Complex.norm_div`
    -- cannot match.  Per `tactics/rw.md`, `rw` takes the leftmost outermost
    -- match, so the negation is not incidental -- it is what the chain built.
    --
    -- Repair: drop `dist_comm` and `zero_sub` entirely.  `mem_closedBall`
    -- already states `dist w 0 ≤ 1`, and `dist_eq_norm` turns that into
    -- `‖w - 0‖`; `sub_zero` then leaves the norm argument as the bare
    -- division `1 / (φ m : ℂ)`, which is the shape `Complex.norm_div` wants.
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Complex.norm_div,
      norm_one, Complex.norm_natCast]
    -- The goal is now `(1 : ℝ) / (φ m : ℝ) ≤ 1`.  `div_le_one₀ (hb : 0 < b)
    -- : a / b ≤ 1 ↔ a ≤ b` (Mathlib/Algebra/Order/GroupWithZero/Unbundled/
    -- Basic.lean:1154) turns it into `1 ≤ (φ m : ℝ)`.  Both casts are supplied
    -- as *stated ℝ facts* rather than left to `omega`, so no tactic is asked to
    -- cross the ℕ/ℝ boundary -- that is the E02 failure mode.
    have hφmR : (0 : ℝ) < (φ m : ℝ) := Nat.cast_pos.mpr (by omega)
    have honeR : (1 : ℝ) ≤ (φ m : ℝ) := by
      -- `Nat.cast_le : (m : α) ≤ n ↔ m ≤ n` (Mathlib/Data/Nat/Cast/Order/
      -- Basic.lean:76); `hφm : 2 ≤ φ m` is strictly stronger than `1 ≤ φ m`.
      -- CE 6449 E02: `exact Nat.cast_le.mpr hφm` was supplied where
      -- `1 ≤ ↑(φ m)` is expected, and `hφm : 2 ≤ φ m` gives `↑2 ≤ ↑(φ m)` --
      -- strictly stronger, hence a type mismatch.  Weakening it in ℕ first and
      -- casting the weakened fact keeps the supplied term's type equal to the
      -- expected type exactly.
      -- CE 6464 E01 (the one independent group in that report): the
      -- previous term was `Nat.le_trans hm2.le hφm`.  `hm2` is the plain
      -- fact `2 <= m`; it is not a structure, so `hm2.le` is an invalid
      -- field projection -- exactly what the compiler reported
      -- (`Invalid field 'le': ... Nat.le.le`).  The weakening step is
      -- `Nat.le_succ (n-1) : n-1 <= n` applied at `n = 2`, which gives
      -- `1 <= 2` (SuccPred/Basic.lean:143), and that composes with `hφm`.
      -- CE 6477 E01: bare `Nat.cast_le.mpr` left its codomain `α` a
      -- metavariable, so the goal state was `CharZero ?m.527` and instance
      -- synthesis failed.  `Nat.cast_le` is declared in the section
      -- `variable [CharZero α] {m n : ℕ}`
      -- (Mathlib/Data/Nat/Cast/Order/Basic.lean:58,69), so `α` is NOT
      -- determined by the two ℕ endpoints -- it is a free implicit, and
      -- the expected type must pin it.  The ascription `(1 : ℝ)` fixes
      -- `α = ℝ`, which carries both `CharZero` and `NatCast`
      -- (instNatCast, Mathlib/Data/Real/Basic.lean:172).
      -- Variant B: avoid `Nat.cast_le` altogether.  `exact_mod_cast` uses
      -- `Nat.cast_le.mpr` internally but pins the codomain from the
      -- EXPECTED type of the goal (`(1 : ℝ) <= (φ m : ℝ)`) rather than
      -- leaving `α` to be solved from the arguments, so it cannot get
      -- stuck on `CharZero ?m`.  The ℕ source fact is unchanged.
      exact_mod_cast (Nat.le_succ 1).trans hφm
    exact (div_le_one₀ hφmR).2 honeR
  -- `f n z` is `fun n z => (n : ℂ) - (n : ℂ)^2 * z` and here `n = φ m`, so
  -- `f (φ m) z = (φ m : ℂ) - (φ m : ℂ)^2 * z` definitionally.
  have hgt := hN m hmN _ hw
  -- The value there is zero: `(φ m)^2 * (1 / (φ m) : ℂ) = (φ m : ℂ)`.
  have hsq : (φ m : ℂ) ^ 2 * (1 / (φ m : ℂ)) = (φ m : ℂ) := by
    -- CE 6421 E04: same pushed-cast cause as E03, now discharged by rewriting
    -- into the ℂ-division form.  The chain is ordered so that each rewrite has
    -- an occurrence to act on:
    --   `pow_two`  exposes the square as `a * a`,
    --   `one_div`  exposes the single surviving `a⁻¹` in ℂ,
    --   `mul_assoc` brings that `a⁻¹` next to an `a`,
    --   `mul_inv_cancel₀` (Mathlib/Algebra/GroupWithZero/Defs.lean:239) cancels
    --   them, and `mul_one` closes.
    -- `field_simp` is not used: in CE 6401 it left `↑(φ m) ^ 2 / ↑↑(φ m)`,
    -- because the ℝ cast still sat inside the division.
    have hφmC : (φ m : ℂ) ≠ 0 := by
      -- ℂ has no order, so `ne_of_gt` is unavailable here.  `Nat.cast_ne_zero
      -- : (↑n : R) ≠ 0 ↔ n ≠ 0` (Mathlib/Algebra/CharZero/Defs.lean:74) is the
      -- standard ℕ → ℂ bridge (cf. Mathlib/Analysis/SpecialFunctions/Gamma/
      -- Beta.lean:263); `.mpr` reads the ℕ side, which `hφm : 2 ≤ φ m` denies.
      exact Nat.cast_ne_zero.mpr (by omega)
    rw [pow_two, one_div, mul_assoc, mul_inv_cancel₀ hφmC, mul_one]
  -- CE 6383 E02: `show T at h` is not grammatical Lean — `at` belongs to
  -- `rw`/`simp`/`filter_upwards`, and `show … at …` parses as the unexpected
  -- token `at`.  The statement is therefore transported by `have`, which is the
  -- supported way to restate a hypothesis.
  have hgt' : (1 : ℝ) < ‖(φ m : ℂ) - (φ m : ℂ) ^ 2 * (1 / (φ m : ℂ))‖ := hgt
  rw [hsq, sub_self, norm_zero] at hgt'
  norm_num at hgt'

-- Prove2me | solution 1 for GeometricSums.geom_sum_le_top_Icc
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:58:14.57582+00:00
-- url     : https://prove2.me/submissions/e59d1315-afe5-45d8-bc97-22f2c8a0ac7e

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Tactic.DyadicRec =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# `DyadicRec` — the dyadic-assembly schema (tactic ledger T6/T9, rung (a))

Harvest of the **dyadic-assembly** proof shape that recurs across the BV/LS
tracks (schema criterion, `docs/blueprints/tactics.md` T9).  The shape is:
"fibre a conductor/scale index dyadically (`Nat.log 2 (f-1)`), obtain a
per-block bound, then close with a geometric sum dominated at the top or the
bottom."  It CANNOT be a single proposition — the recurring object is a proof
shape with a *motive hole* (the per-block bound `B`, and the eliminator's
per-level bound `blk`) — so it is captured here at ladder rung (a): higher-order
LEMMAs with a motive, applied directly or via `induction … using`.

## The five studied instances

| instance | file | role in the schema |
|---|---|---|
| `interval_decomp` | `Salt/BV/MaxLS.lean` | the strict-length dyadic **eliminator** |
| `dyadic` (BDH) | `Salt/LS/BDH.lean` | `Nat.log 2 (f-1)` conductor **fibering** + geom close |
| `typeII_disc_reduce` | `Salt/BV/TypeII.lean` | fibering with a conductor **cutoff** (`Icc lo`) |
| `dsA_bound … dsD_bound` | `Salt/BV/TypeIIClose.lean` | the four **geometric-close** regimes |
| the divisor swap | `Salt/LS/PhiSum.lean` | adjacent (a `sum_comm` reindex, T6 — not dyadic) |

## The three artifacts

1. **`dyadic_cover_sum_le` / `_range`** — the fibering.  `∑_{f∈S} g f ≤ ∑_i B i`
   over the dyadic blocks `Nat.log 2 (f-1) = i`, parameterized by the per-block
   bound `B` (the motive hole).  `mem_dyadic_block` is the reusable block-
   membership fact both fibering instances re-prove inline.
2. **`geom_sum_le_top` / `geom_sum_le_bot`** (+ `_Icc` variants + `r∈{2,√2,½,1/√2}`
   corollaries) — the domination pair every dyadic assembly ends in.
3. **`dyadic_interval_rec`** — the eliminator, abstracting `interval_decomp`'s
   `≤ 1-block-per-level` strict-length induction from its `sup'` block bound to
   an arbitrary per-level bound `blk`.

### "Could-have-consumed" audit (design check — NO retrofit performed)

* `BDH.dyadic` (`Salt/LS/BDH.lean:243,311`): `rw [← sum_fiberwise_of_maps_to hmaps g]`
  then `(sum_le_sum hfiber).trans` **is exactly** `dyadic_cover_sum_le_range`
  (`S = Icc 2 Q`, `b = Q`, `B j = (1/2^j)((2^{j+1})²+13(x+1))·SL2`).  The
  geometric close (`hgeom1`, `hgeom2`) is `geom_two_pow_range_le` (r=2, top) and
  `geom_half_range_le` (r=½, bot).
* `TypeII.typeII_disc_reduce` (`Salt/BV/TypeII.lean:411-443`): the inner
  `sum_fiberwise_of_maps_to hmaps` into `Icc imin I` **is exactly**
  `dyadic_cover_sum_le` (`lo = imin` from the `(log x)^C < f` cutoff, `hi = I`).
  The `Icc (2^i) (2·2^i)` block-containment (lines 434-438) is `mem_dyadic_block`.
* `TypeIIClose.dsA/dsB/dsC/dsD` (`Salt/BV/TypeIIClose.lean:457-598`): the four
  closes are `geom_sum_le_top_Icc` (dsA, r=2), `geom_sum_le_bot`/`sum_inv_sqrt_dyadic`
  (dsB, r=1/√2), `geom_sum_le_top`/`sum_sqrt_dyadic` (dsC, r=√2), and
  `geom_sum_le_bot_Icc` (dsD, r=½) — after each factors its `√U`/scale prefix.
  `sum_two_pow_Icc_le` = `geom_sum_le_top_Icc (c=1)(r=2)` + `2^{b+1} ≤ 2Q`.
* `MaxLS.interval_decomp` (`Salt/BV/MaxLS.lean:104`) **is**
  `dyadic_interval_rec (fun n => c n * χ n) N (fun j => sup'_j …) hsup_nonneg
  (fun j a h h' => single_block_le χ c N hNne j a h h') m`.

## Assessment of the other T9 candidates

**`regime_split`** (the `√(a+b) ≤ √a+√b` four-regime budget expansion —
`AnalyticLS`, `BDH`, `blockBound_le_regimes`): its reusable *core*,
`sqrt_add_le`, is ALREADY a landed public lemma (`Salt/BV/TypeIIClose.lean:26`),
and the 4-way product distribution `(√A+√B)(√C+√D) = √A√C+…` is `nlinarith`-
shaped.  What is problem-specific is the *assignment* of which regime dominates
(which term is `√x·Q` vs `x/√U` …).  Evidence today: exactly ONE full 4-regime
instance (`blockBound_le_regimes`) plus ~2 loose `sqrt_add_le` uses.  **Verdict:
lemma-able core already landed; a rung-(b) macro is plausible but NOT-YET
justified** (needs a 2nd full instance to generalize the regime-labelling from).

**`guard_collapse`** (vanishing-factor filter elimination — `typeII_le_sum_blocks`'s
empty-tail `hempty`+`sum_subset` (`Salt/BV/TypeII.lean:401-412`), MulChar off-units,
`lamPhiContractM` off-box): the *move* is `Finset.sum_subset`/`sum_filter_of_ne`
with an off-set-vanishes discharge — both already mathlib lemmas.  The
value-add would be automating the "vanishes" proof, but across the three cited
tracks the vanish reasons are structurally UNrelated (an empty filtered set from
`y < d·m`; a character being `0` off the units; a box cutoff), so no single
lemma or uniform discharge captures them.  **Verdict: NOT-YET (heterogeneous
discharge); the existing `Finset.sum_subset` family already serves; revisit iff
a common vanish-shape emerges.**
-/

namespace Salt.Tactic

open Finset

/-! ## Section 1 — the dyadic fibering (`dyadic_cover_sum_le`) -/

/-- **Dyadic block membership.**  If `2 ≤ f` and `Nat.log 2 (f-1) = i`, then `f`
lies in the `i`-th dyadic block: `2^i < f ≤ 2^{i+1}`.  This is the fact both
fibering instances (`BDH.dyadic`, `TypeII.typeII_disc_reduce`) re-prove inline to
extend a `Nat.log`-fibre to an `Icc (2^i) (2·2^i)`. -/
lemma mem_dyadic_block {f i : ℕ} (hf : 2 ≤ f) (hlog : Nat.log 2 (f - 1) = i) :
    2 ^ i < f ∧ f ≤ 2 ^ (i + 1) := by
  have hf1 : f - 1 ≠ 0 := by omega
  have hlow : 2 ^ i ≤ f - 1 := hlog ▸ Nat.pow_log_le_self 2 hf1
  have hhigh : f - 1 < 2 ^ (i + 1) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (f - 1)
    rwa [hlog] at h
  omega

/-- **The dyadic fibering (cut form).**  For `S ⊆ Icc a b` fibred by
`Nat.log 2 (f-1)`, with a lower cut `lo` guaranteed by `hlo` (the conductor
cutoff in `TypeII`), the whole sum is bounded by the per-block sum over
`Icc lo (Nat.log 2 (b-1))`, given a per-block bound `hblock` (the motive hole).

`TypeII.typeII_disc_reduce`'s inner `sum_fiberwise_of_maps_to hmaps` into
`Icc imin I` (`Salt/BV/TypeII.lean:411`) is exactly this, with `lo = imin`. -/
theorem dyadic_cover_sum_le {S : Finset ℕ} {a b lo : ℕ} (hS : S ⊆ Finset.Icc a b)
    (hlo : ∀ f ∈ S, lo ≤ Nat.log 2 (f - 1)) (g : ℕ → ℝ) (B : ℕ → ℝ)
    (hblock : ∀ i ∈ Finset.Icc lo (Nat.log 2 (b - 1)),
        ∑ f ∈ S.filter (fun f => Nat.log 2 (f - 1) = i), g f ≤ B i) :
    ∑ f ∈ S, g f ≤ ∑ i ∈ Finset.Icc lo (Nat.log 2 (b - 1)), B i := by
  have hmaps : ∀ f ∈ S, Nat.log 2 (f - 1) ∈ Finset.Icc lo (Nat.log 2 (b - 1)) := by
    intro f hf
    have hfb := hS hf; rw [Finset.mem_Icc] at hfb
    rw [Finset.mem_Icc]
    exact ⟨hlo f hf, Nat.log_mono_right (by omega)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps g]
  exact Finset.sum_le_sum hblock

/-- **The dyadic fibering (range form, `lo = 0`).**  `BDH.dyadic`'s
`rw [← sum_fiberwise_of_maps_to hmaps g]` + `(sum_le_sum hfiber).trans`
(`Salt/LS/BDH.lean:243,311`) is exactly this, with `S = Icc 2 Q`, `b = Q`. -/
theorem dyadic_cover_sum_le_range {S : Finset ℕ} {a b : ℕ} (hS : S ⊆ Finset.Icc a b)
    (g : ℕ → ℝ) (B : ℕ → ℝ)
    (hblock : ∀ i ∈ Finset.range (Nat.log 2 (b - 1) + 1),
        ∑ f ∈ S.filter (fun f => Nat.log 2 (f - 1) = i), g f ≤ B i) :
    ∑ f ∈ S, g f ≤ ∑ i ∈ Finset.range (Nat.log 2 (b - 1) + 1), B i := by
  have hmaps : ∀ f ∈ S, Nat.log 2 (f - 1) ∈ Finset.range (Nat.log 2 (b - 1) + 1) := by
    intro f hf
    have hfb := hS hf; rw [Finset.mem_Icc] at hfb
    rw [Finset.mem_range]
    have := Nat.log_mono_right (b := 2) (show f - 1 ≤ b - 1 by omega)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps g]
  exact Finset.sum_le_sum hblock

/-! ## Section 2 — the geometric domination pair (`geom_sum_le_top`/`_bot`) -/

/-- `√2 ≥ 4/3`. -/
private lemma sqrt2_ge : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]

/-- `1 < √2`. -/
private lemma sqrt2_gt_one : (1 : ℝ) < Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]

/-- **Top-dominated geometric sum** (`r > 1`).  `∑_{i<I} c·rⁱ ≤ c·rᴵ/(r-1)`.
The increasing regime: the top term dominates.  Closed form for `dsC` (`r=√2`)
and `dsA` (`r=2`) after the scale prefix is factored. -/
lemma geom_sum_le_top {r c : ℝ} (hc : 0 ≤ c) (hr : 1 < r) (I : ℕ) :
    ∑ i ∈ Finset.range I, c * r ^ i ≤ c * r ^ I / (r - 1) := by
  have hpos : (0 : ℝ) < r - 1 := by linarith
  rw [← Finset.mul_sum, geom_sum_eq (by linarith : r ≠ 1), mul_div_assoc]
  gcongr
  linarith

/-- **Bottom-dominated geometric sum** (`0 ≤ r < 1`).  `∑_{i<I} c·rⁱ ≤ c/(1-r)`.
The decreasing regime: the whole (infinite) tail sums to `1/(1-r)`, independent
of `I`.  Closed form for `BDH`'s `1/2` and `dsB`'s `1/√2` (after the prefix). -/
lemma geom_sum_le_bot {r c : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1) (I : ℕ) :
    ∑ i ∈ Finset.range I, c * r ^ i ≤ c / (1 - r) := by
  rw [← Finset.mul_sum, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left
    (sum_le_hasSum _ (fun i _ => pow_nonneg hr0 i) (hasSum_geometric_of_lt_one hr0 hr1)) hc

/-- **Top-dominated, `Icc` form** (`r > 1`).  `∑_{i∈Icc a b} c·rⁱ ≤ c·r^{b+1}/(r-1)`.
`dsA`'s `sum_two_pow_Icc_le` = this at `c=1, r=2` (then `2^{b+1} ≤ 2Q`). -/
lemma geom_sum_le_top_Icc {r c : ℝ} (hc : 0 ≤ c) (hr : 1 < r) (a b : ℕ) :
    ∑ i ∈ Finset.Icc a b, c * r ^ i ≤ c * r ^ (b + 1) / (r - 1) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (geom_sum_le_top hc hr (b + 1))
  · intro i hi; rw [Finset.mem_Icc] at hi; rw [Finset.mem_range]; omega
  · intro i _ _; exact mul_nonneg hc (pow_nonneg (by linarith) i)

/-- **Bottom-dominated, `Icc` form** (`0 ≤ r < 1`).  `∑_{i∈Icc a b} c·rⁱ ≤ c·rᵃ/(1-r)`.
`dsD`'s `sum_half_Icc_le` = this at `c=1, r=1/2` (`rᵃ·2 = 2·(1/2)ᵃ`). -/
lemma geom_sum_le_bot_Icc {r c : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1) (a b : ℕ) :
    ∑ i ∈ Finset.Icc a b, c * r ^ i ≤ c * r ^ a / (1 - r) := by
  have hIcc : Finset.Icc a b = Finset.Ico a (b + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hrw : ∀ k, c * r ^ (a + k) = (c * r ^ a) * r ^ k := fun k => by rw [pow_add]; ring
  simp_rw [hrw]
  exact geom_sum_le_bot (mul_nonneg hc (pow_nonneg hr0 a)) hr0 hr1 (b + 1 - a)

/-- Corollary (top, `r = 2`, `BDH.hgeom1` / dsA core): `∑_{i<I} 2ⁱ ≤ 2ᴵ`. -/
lemma geom_two_pow_range_le (I : ℕ) : ∑ i ∈ Finset.range I, (2 : ℝ) ^ i ≤ 2 ^ I := by
  have h := geom_sum_le_top (c := 1) (r := 2) (by norm_num) (by norm_num) I
  simp only [one_mul] at h
  rw [show (2 : ℝ) - 1 = 1 by norm_num, div_one] at h
  exact h

/-- Corollary (top, `r = √2`, dsC core `sum_sqrt_dyadic.hgeom`):
`∑_{j<J} (√2)ʲ ≤ 3·(√2)ᴶ`. -/
lemma geom_sqrt_two_pow_le (J : ℕ) :
    ∑ j ∈ Finset.range J, Real.sqrt 2 ^ j ≤ 3 * Real.sqrt 2 ^ J := by
  have htop := geom_sum_le_top (c := 1) (r := Real.sqrt 2) (by norm_num) sqrt2_gt_one J
  have hpow : (0 : ℝ) ≤ Real.sqrt 2 ^ J := by positivity
  have hle3 : (1 : ℝ) * Real.sqrt 2 ^ J / (Real.sqrt 2 - 1) ≤ 3 * Real.sqrt 2 ^ J := by
    rw [one_mul, div_le_iff₀ (by nlinarith [sqrt2_gt_one] : (0 : ℝ) < Real.sqrt 2 - 1)]
    nlinarith [hpow, mul_nonneg hpow (show (0 : ℝ) ≤ 3 * Real.sqrt 2 - 4 by nlinarith [sqrt2_ge])]
  calc ∑ j ∈ Finset.range J, Real.sqrt 2 ^ j
      = ∑ j ∈ Finset.range J, (1 : ℝ) * Real.sqrt 2 ^ j := by simp
    _ ≤ 1 * Real.sqrt 2 ^ J / (Real.sqrt 2 - 1) := htop
    _ ≤ 3 * Real.sqrt 2 ^ J := hle3

/-- Corollary (bot, `r = 1/2`, `BDH.hgeom2`): `∑_{i<I} (1/2)ⁱ ≤ 2`. -/
lemma geom_half_range_le (I : ℕ) : ∑ i ∈ Finset.range I, (1 / 2 : ℝ) ^ i ≤ 2 := by
  have h := geom_sum_le_bot (c := 1) (r := 1 / 2) (by norm_num) (by norm_num) (by norm_num) I
  simp only [one_mul] at h
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  norm_num at h
  exact h

/-- Corollary (bot, `r = 1/√2`, dsB core `sum_inv_sqrt_dyadic`):
`∑_{j<J} (1/√2)ʲ ≤ 4`. -/
lemma geom_inv_sqrt_two_le (J : ℕ) :
    ∑ j ∈ Finset.range J, (1 / Real.sqrt 2) ^ j ≤ 4 := by
  have hr0 : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
  have hr1 : (1 / Real.sqrt 2 : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]; exact sqrt2_gt_one
  have hbot := geom_sum_le_bot (c := 1) (by norm_num) hr0 hr1 J
  have hden : (0 : ℝ) < 1 - 1 / Real.sqrt 2 := by rw [sub_pos]; exact hr1
  have hsp : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hle4 : (1 : ℝ) / (1 - 1 / Real.sqrt 2) ≤ 4 := by
    rw [div_le_iff₀ hden]
    have h1s : (1 : ℝ) / Real.sqrt 2 ≤ 3 / 4 := by
      rw [div_le_div_iff₀ hsp (by norm_num)]; nlinarith [sqrt2_ge]
    nlinarith [h1s]
  calc ∑ j ∈ Finset.range J, (1 / Real.sqrt 2) ^ j
      = ∑ j ∈ Finset.range J, (1 : ℝ) * (1 / Real.sqrt 2) ^ j := by simp
    _ ≤ 1 / (1 - 1 / Real.sqrt 2) := hbot
    _ ≤ 4 := hle4

/-- **Demonstration (geometric close).**  A top-dominated dyadic geometric sum
closed in 2 lines; by hand this is `geom_sum_eq` + the `(rᴵ-1)/(r-1) ≤ rᴵ/(r-1)`
division estimate + the `mul_le_mul` plumbing (~15 lines). -/
example (n : ℕ) : ∑ i ∈ Finset.range n, (3 : ℝ) * 2 ^ i ≤ 3 * 2 ^ n := by
  have h := geom_sum_le_top (c := 3) (r := 2) (by norm_num) (by norm_num) n
  rw [show (2 : ℝ) - 1 = 1 by norm_num, div_one] at h
  exact h

/-- **Demonstration (fibering + geometric close — the whole schema).**  A count
bound assembled through §1 then §2: fibre `Icc 2 8` dyadically, bound each block
by its size `2^i` (via `mem_dyadic_block`), close with `geom_two_pow_range_le`.
By hand this is the full `Nat.log`-maps-to + `sum_fiberwise` + geometric plumbing
(~40 lines); here it is ~10.  (The bound `2^(Nat.log 2 7 + 1)` equals `8`.) -/
example : ∑ _f ∈ Finset.Icc 2 8, (1 : ℝ) ≤ 2 ^ (Nat.log 2 (8 - 1) + 1) := by
  refine (dyadic_cover_sum_le_range (a := 2) (b := 8) (Finset.Subset.refl _)
    (fun _ => 1) (fun i => (2 : ℝ) ^ i) ?_).trans (geom_two_pow_range_le _)
  intro i _
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsub : (Finset.Icc 2 8).filter (fun f => Nat.log 2 (f - 1) = i)
      ⊆ Finset.Icc (2 ^ i + 1) (2 ^ (i + 1)) := by
    intro f hf
    rw [Finset.mem_filter, Finset.mem_Icc] at hf
    obtain ⟨⟨hf2, _⟩, hlog⟩ := hf
    have := mem_dyadic_block hf2 hlog
    rw [Finset.mem_Icc]; omega
  calc (((Finset.Icc 2 8).filter (fun f => Nat.log 2 (f - 1) = i)).card : ℝ)
      ≤ ((Finset.Icc (2 ^ i + 1) (2 ^ (i + 1))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (2 : ℝ) ^ i := by
        rw [Nat.card_Icc]
        have : 2 ^ (i + 1) + 1 - (2 ^ i + 1) = 2 ^ i := by rw [pow_succ]; omega
        rw [this]; push_cast; ring

/-! ## Section 3 — the dyadic interval eliminator (`dyadic_interval_rec`) -/

/-- **Dyadic interval eliminator** (rung (a)).  Any `2^m`-aligned interval `[a,b)`
of length `< 2^m` decomposes into at most one dyadic block per level `j < m`;
hence if every aligned single block of length `2^j` (starting at a `2^j`-multiple,
staying `≤ N`) has `‖∑ F‖ ≤ blk j`, the whole interval sum obeys
`‖∑_{[a,b)} F‖ ≤ ∑_{j<m} blk j`.

This abstracts `Salt.BV.interval_decomp` (`Salt/BV/MaxLS.lean:104`) — its sole
natural client — from the specific `sup'` block bound to an arbitrary per-level
`blk`; the fibering instances (§1) are NOT eliminator-shaped, so this is the one
genuine `induction … using` artifact.  `interval_decomp` is recovered as
`dyadic_interval_rec (fun n => c n * χ n) N (fun j => sup'_j) hsup_nonneg
(fun j a h h' => single_block_le χ c N hNne j a h h') m`. -/
theorem dyadic_interval_rec {G : Type*} [NormedAddCommGroup G] (F : ℕ → G) (N : ℕ)
    (blk : ℕ → ℝ) (hblk_nn : ∀ j, 0 ≤ blk j)
    (hsingle : ∀ j a, 2 ^ j ∣ a → a + 2 ^ j ≤ N →
      ‖∑ n ∈ Finset.Ico a (a + 2 ^ j), F n‖ ≤ blk j)
    (m : ℕ) : ∀ a b : ℕ, 2 ^ m ∣ a → a ≤ b → b < a + 2 ^ m → b ≤ N →
      ‖∑ n ∈ Finset.Ico a b, F n‖ ≤ ∑ j ∈ Finset.range m, blk j := by
  induction m with
  | zero =>
    intro a b _ hab hb _
    have hba : b = a := by simp only [pow_zero] at hb; omega
    subst hba; simp
  | succ m ih =>
    intro a b hdvd hab hb hbN
    have hdvd_m : 2 ^ m ∣ a := dvd_trans (pow_dvd_pow 2 (Nat.le_succ m)) hdvd
    by_cases hbc : b ≤ a + 2 ^ m
    · by_cases hbc2 : b < a + 2 ^ m
      · refine le_trans (ih a b hdvd_m hab hbc2 hbN) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (Nat.le_succ m)) (fun j _ _ => hblk_nn j)
      · have hbeq : b = a + 2 ^ m := by omega
        subst hbeq
        refine le_trans (hsingle m a hdvd_m hbN) ?_
        exact Finset.single_le_sum (fun j _ => hblk_nn j)
          (Finset.mem_range.mpr (Nat.lt_succ_self m))
    · have hle1 : a ≤ a + 2 ^ m := Nat.le_add_right a _
      have hle2 : a + 2 ^ m ≤ b := by omega
      rw [← Finset.sum_Ico_consecutive F hle1 hle2]
      refine le_trans (norm_add_le _ _) ?_
      have hblkm : ‖∑ n ∈ Finset.Ico a (a + 2 ^ m), F n‖ ≤ blk m :=
        hsingle m a hdvd_m (by omega)
      have hdvd_m' : 2 ^ m ∣ (a + 2 ^ m) := dvd_add hdvd_m (dvd_refl _)
      have hrest : ‖∑ n ∈ Finset.Ico (a + 2 ^ m) b, F n‖ ≤ ∑ j ∈ Finset.range m, blk j :=
        ih (a + 2 ^ m) b hdvd_m' hle2 (by rw [pow_succ] at hb; omega) hbN
      calc ‖∑ n ∈ Finset.Ico a (a + 2 ^ m), F n‖ + ‖∑ n ∈ Finset.Ico (a + 2 ^ m) b, F n‖
          ≤ blk m + ∑ j ∈ Finset.range m, blk j := add_le_add hblkm hrest
        _ = ∑ j ∈ Finset.range (m + 1), blk j := by rw [Finset.sum_range_succ]; ring

/-- **Demonstration (eliminator).**  If every aligned dyadic single block of `F`
has sum-norm `≤ 1`, then any `2^m`-aligned short interval has sum-norm `≤ m`.  By
hand this is the full strict-length induction (~40 lines); via the eliminator it
is one application. -/
example (F : ℕ → ℝ) (m : ℕ)
    (hs : ∀ j a, 2 ^ j ∣ a → ‖∑ n ∈ Finset.Ico a (a + 2 ^ j), F n‖ ≤ 1) :
    ‖∑ n ∈ Finset.Ico 0 (2 ^ m - 1), F n‖ ≤ m := by
  have hp : 0 < 2 ^ m := pow_pos (by norm_num) m
  have h := dyadic_interval_rec F (2 ^ m) (fun _ => 1) (fun _ => by norm_num)
    (fun j a hdvd _ => hs j a hdvd) m 0 (2 ^ m - 1) (dvd_zero _) (Nat.zero_le _)
    (by omega) (by omega)
  simpa using h

end Salt.Tactic

end




section
open Finset

theorem solution {r c : ℝ} (hc : 0 ≤ c) (hr : 1 < r) (a b : ℕ) :
    ∑ i ∈ Finset.Icc a b, c * r ^ i ≤ c * r ^ (b + 1) / (r - 1) := by
  apply Salt.Tactic.geom_sum_le_top_Icc <;> assumption

end


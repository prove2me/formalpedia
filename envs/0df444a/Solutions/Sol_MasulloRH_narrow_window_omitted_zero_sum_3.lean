-- Prove2me | solution 3 for MasulloRH.narrow_window_omitted_zero_sum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:33:10.802676+00:00
-- url     : https://prove2.me/submissions/26fc386b-4786-400e-a47b-a7bb87749852
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_MasulloRH_zero_free_right

open MeasureTheory Set MasulloRH ConnesRZ

/-- DESIGN DRAFT — UNVERIFIED. Not compiled, not submitted.

SKETCH proof of `MasulloRH.narrow_window_omitted_zero_sum`
(id 6d631fe7-ce53-4f51-b660-706b2183ed5d, Open) from the open node
`MasulloRH.zero_free_right` (id 12360d46-f4ac-4dcc-93d2-06be16c15a38, Open;
statement fetched verbatim via `p2m.py theorem`):

  `theorem MasulloRH.zero_free_right (s : ℂ) (hs : (1/2 : ℝ) < s.re)
      (hs_one : s ≠ 1) : riemannZeta s ≠ 0`

This is a *reduction*, not a proof: `zero_free_right` is itself RH-strength.
The mathematical point is that the implication needs nothing else — the
omitted subtype is shown EMPTY, and a `tsum` over an empty type is `0`
(`tsum_empty`, verified in `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean`).

Emptiness argument. Let `r : omitted`, `ρ := r.val.val : ℂ`. Then
`r.val.property : ConnesRZ.IsCriticalZero ρ`, i.e. (by the definition in
`Definitions.Def_ConnesRZ_weil_defs`) `riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1`,
and `r.property : α ≤ |ρ.re - 1/2|`. In particular `ρ.re ≠ 1/2` (else
`|ρ.re - 1/2| = 0 < α`, using `hα`), so exactly one of:

* (i) `ρ.re > 1/2`: `zero_free_right` at `ρ` applies directly — `ρ ≠ 1`
  because `ρ.re < 1 = (1 : ℂ).re` — and contradicts `riemannZeta ρ = 0`.
* (ii) `ρ.re < 1/2`: reflect. The functional equation gives
  `riemannZeta (1 - ρ) = 0` (helper `hsymm` below), `(1 - ρ).re = 1 - ρ.re
  > 1/2`, and `1 - ρ ≠ 1` because `(1 - ρ).re = 1 - ρ.re < 1 = (1 : ℂ).re`
  (using `ρ.re > 0`); `zero_free_right` at `1 - ρ` gives the contradiction.

Symmetry route (researched in local Mathlib, rev 0df444a — the cleanest
route found needs NO Gamma-factor nonvanishing): Mathlib's un-completed
functional equation

  `riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
     riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2)
       * riemannZeta s`

(`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`, the lemma immediately
preceding the `RiemannHypothesis` definition) expresses `ζ (1 - s)` as an
explicit factor TIMES `ζ s`, so `ζ s = 0` gives `ζ (1 - s) = 0` by rewriting
alone. Its two side hypotheses are discharged from `0 < ρ.re < 1` by real
parts: `ρ ≠ -(n : ℂ)` since `(-(n : ℂ)).re = -(n : ℝ) ≤ 0 < ρ.re`, and
`ρ ≠ 1` since `ρ.re < 1`.

The heavier alternative route — `completedRiemannZeta_one_sub`
(`Λ (1 - s) = Λ s`, same file) combined with
`riemannZeta_def_of_ne_zero : riemannZeta s = completedRiemannZeta s /
Gammaℝ s` and `Complex.Gamma_ne_zero` / `Complex.Gamma_ne_zero_of_re_pos`
(`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`, lines 427 / 454) to
strip the factor `π ^ (-s/2) * Gamma (s / 2)` at both `ρ` and `1 - ρ` — also
exists, but is strictly more work (it additionally has to handle the
`s = 0` correction in `completedRiemannZeta` and the `Gammaℝ` unfolding).
It is recorded here only as a fallback if `riemannZeta_one_sub`'s exact
form shifts.

Known soft spots (coordinator: check these first at build time):
* The goal's `omitted` is a `let`; `haveI := hEmpty` + `exact tsum_empty`
  relies on defeq between the let-bound type and the explicit subtype in
  `hEmpty`. Fallbacks, in order (cf. `work/t1-capstone/notes.md` pitfall 1):
  `dsimp only` at the goal; a `show` restating the goal over the explicit
  subtype; a standalone `have` proved by `exact`.
* `obtain ⟨hζ, h0, h1⟩ := r.val.property` relies on `rcases` whnf-unfolding
  the plain `def ConnesRZ.IsCriticalZero` (same pattern as the accepted
  `work/t1-capstone/spectral_sketch.lean`); if it balks, insert
  `have hcrit : riemannZeta _ = 0 ∧ _ ∧ _ := r.val.property` first.
* In `hsymm`, the hypothesis of `riemannZeta_one_sub` is stated there as
  `∀ n : ℕ, s ≠ -n`; `hρnn` is phrased as `ρ ≠ -(n : ℂ)` for the same term.
* No placeholder/admit tactics are used anywhere in this draft. -/
theorem solution (α : ℝ) (hα : 0 < α) (hsmall : α < 1 / 2)
    (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
    (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0 := by
  -- Step 1: functional-equation symmetry — a critical-strip zero reflects to
  -- a critical-strip zero. Via `riemannZeta_one_sub`, no Gamma input needed.
  have hsymm : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      riemannZeta (1 - ρ) = 0 := by
    intro ρ hζ h0 h1
    have hρnn : ∀ n : ℕ, ρ ≠ -(n : ℂ) := by
      intro n hn
      have hre : ρ.re = -(n : ℝ) := by simpa using congrArg Complex.re hn
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hρ1 : ρ ≠ 1 := by
      intro h
      have hre : ρ.re = (1 : ℂ).re := congrArg Complex.re h
      rw [Complex.one_re] at hre
      linarith
    have hFE := riemannZeta_one_sub hρnn hρ1
    rw [hζ, mul_zero] at hFE
    exact hFE
  -- Step 2: the omitted subtype is empty.
  have hEmpty : IsEmpty {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|} := by
    refine ⟨fun r => ?_⟩
    obtain ⟨hζ, h0, h1⟩ := r.val.property
    have hge : α ≤ |r.val.val.re - 1 / 2| := r.property
    rcases lt_trichotomy r.val.val.re (1 / 2 : ℝ) with hlt | heq | hgt
    · -- Case (ii): `ρ.re < 1/2` — reflect to `1 - ρ` and apply `zero_free_right` there.
      have hζ' : riemannZeta (1 - r.val.val) = 0 := hsymm r.val.val hζ h0 h1
      have hre : (1 - r.val.val).re = 1 - r.val.val.re := by
        rw [Complex.sub_re, Complex.one_re]
      have hgt' : (1 / 2 : ℝ) < (1 - r.val.val).re := by
        rw [hre]; linarith
      have hne : (1 - r.val.val) ≠ 1 := by
        intro h
        have hre1 : (1 - r.val.val).re = (1 : ℂ).re := congrArg Complex.re h
        rw [hre, Complex.one_re] at hre1
        linarith
      exact (MasulloRH.zero_free_right (1 - r.val.val) hgt' hne) hζ'
    · -- Middle case: `ρ.re = 1/2` — then `|ρ.re - 1/2| = 0`, contradicting `α ≤ |…|` and `0 < α`.
      have habs : |r.val.val.re - 1 / 2| = 0 := by rw [heq, sub_self, abs_zero]
      rw [habs] at hge
      exact (not_le.mpr hα) hge
    · -- Case (i): `ρ.re > 1/2` — `zero_free_right` at `ρ` directly; `ρ ≠ 1` since `ρ.re < 1`.
      have hne : r.val.val ≠ 1 := by
        intro h
        have hre : r.val.val.re = (1 : ℂ).re := congrArg Complex.re h
        rw [Complex.one_re] at hre
        linarith
      exact (MasulloRH.zero_free_right r.val.val hgt hne) hζ
  -- Step 3: a `tsum` over an empty index type is `0`.
  haveI := hEmpty
  exact tsum_empty

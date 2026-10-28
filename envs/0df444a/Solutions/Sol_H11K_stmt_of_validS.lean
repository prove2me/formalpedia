-- Prove2me | solution 1 for H11K.stmt_of_validS
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:21:18.425177+00:00
-- url     : https://prove2.me/submissions/0e13eb98-c175-430f-b5de-364103bf32d4

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Gamma
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Line
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Seg
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgChangeGlue
import Definitions.Def_ArdaRH65K_Turing121_ArgGammaR
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
import Definitions.Def_ArdaRH65K_Turing121_ArgZetaTwo
import Definitions.Def_ArdaRH65K_Turing121_BandGlue
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabClear
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_H1000Line
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
import Definitions.Def_ArdaRH65K_Turing121_H1000Phase
import Definitions.Def_ArdaRH65K_Turing121_H1000Point
import Definitions.Def_ArdaRH65K_Turing121_H11K_Turing
import Definitions.Def_ArdaRH65K_Turing121_HeightFloorCheck
import Definitions.Def_ArdaRH65K_Turing121_KernelGammaEnvelope
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_H11K_turing_band_on_line_sharp
namespace BandGlue
end BandGlue
namespace BandGlue.BandData
end BandGlue.BandData
/- Task 6 (Stage 3): RH-IN-A-BOX LOCALIZATION CAPSTONE.

   Box `B = [2/5, 3/5] x [10, 35]`.  This file composes the three kernel results of the project into
   the crowning statement: EVERY nontrivial zero of `riemannZeta` in `B` lies on the critical line
   `Re = 1/2` (and is simple).  This is a Turing-style VERIFICATION OF RH INSIDE THIS BOX.  It is NOT
   a proof of the Riemann Hypothesis.  `conjecture1_proved = False`.

   The pieces composed:

   1. TOTAL COUNT = 5 (kernel argument principle):
      `BoxArgPrincipleZeta.box_arg_principle_zeta'` concludes `∃ s d, Σ_{ρ∈s} (d ρ) = N`, where `s`
      is the ACTUAL zeta divisor support on the ball `U = ball cB 13 ⊇ B` and `d` its multiplicity
      (`MeromorphicOn.divisor riemannZeta U`), GIVEN the honest Arb bundle `hArb` at `N = 5`.  The
      winding integer `N = 5`, edge non-vanishing, strict interiority, and the value enclosures are
      the documented NON-KERNEL Arb inputs (same trust boundary as Stage 1's enclosures).

   2. ON-LINE LOWER BOUND >= 5 (kernel, Stage 1):
      `XiLineZeros.lambda_five_zeros_10_35` yields 5 DISTINCT `completedRiemannZeta` zeros on the line
      `Re = 1/2` with imaginary parts in `(10, 35)` (from Arb-certified sign changes).

   3. LAMBDA <-> ZETA BRIDGE (kernel, this file):
      In `B` (`Re > 0`, so `s ≠ 0`), `riemannZeta s = completedRiemannZeta s / Gammaℝ s` with
      `Gammaℝ s ≠ 0`; hence `riemannZeta s = 0 ↔ completedRiemannZeta s = 0`.  The 5 on-line
      `completedRiemannZeta`-zeros ARE 5 distinct on-line `riemannZeta`-zeros in `B`.

   COUNTING ARGUMENT (kernel, this file): the divisor is nonnegative (zeta is analytic on `U`, no
   poles), so `d ρ ≥ 1` at every zero.  The 5 distinct on-line zeros lie in the support `s`, each
   with `d ≥ 1`, summing to `≥ 5`.  Since the TOTAL is exactly `5`, they EXHAUST the divisor: the
   support equals those 5 points and each multiplicity is exactly 1.  Therefore every zeta-zero in
   `B` is one of the 5 on-line zeros -- so it lies on `Re = 1/2` and is simple.

   conjecture1_proved = False. -/




open Complex Real

namespace BoxLocalization

/-! ## Part A: the pure combinatorial localization lemma (kernel).

If a finite multiset-with-multiplicity `d ≥ 1` on a support `s` sums to `n`, and we already exhibit
`n` DISTINCT elements of `s`, then `s` is EXACTLY those `n` elements and every multiplicity is `1`.
This is the load-bearing counting step; it is fully general and kernel-proven. -/



/-! ## Part B: the Lambda <-> zeta bridge on the box (kernel).

On `B` we have `Re > 0`, so `s ≠ 0` and `Gammaℝ s ≠ 0`; then
`riemannZeta s = completedRiemannZeta s / Gammaℝ s`, whence the two functions share their zeros. -/

/-- On a point with positive real part, `riemannZeta ρ = 0 ↔ completedRiemannZeta ρ = 0`. -/
theorem zeta_zero_iff_completed_zero {ρ : ℂ} (hre : 0 < ρ.re) :
    riemannZeta ρ = 0 ↔ completedRiemannZeta ρ = 0 := by
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have hGne : Gammaℝ ρ ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  rw [riemannZeta_def_of_ne_zero hρ0, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hGne
  · intro h; exact Or.inl h

/-- The Stage-1 on-line points `1/2 + t*I` have `Re = 1/2 > 0`, so the bridge applies: a
    `completedRiemannZeta` zero there is a `riemannZeta` zero there. -/
theorem line_zeta_zero_of_completed {t : ℝ}
    (h : completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) :
    riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 := by
  have hre : (0 : ℝ) < (1 / 2 + (t : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    norm_num
  exact (zeta_zero_iff_completed_zero hre).mpr h

/-! ## Part C: membership of on-line zeros in the divisor support.

A `riemannZeta` zero `ρ` inside the ball `U = ball cB 13` lies in the support `s` of the divisor
with multiplicity `d ρ ≥ 1` (zeta is analytic and nonzero-order-1 at a zero). -/



/-! ## Part D: THE CAPSTONE.

Given the honest, generic divisor bundle (which the Blaschke-split / argument-principle produces),
plus the five distinct on-line zeros (Stage 1) and the total count 5, conclude that every zeta-zero
in `B` is on `Re = 1/2` and simple.  Two forms are provided:

* `box_localization_core`: the counting capstone stated over an abstract divisor `s, d` satisfying
  the divisor axioms (support = zeros-in-`U`, `d ≥ 1` at zeros, total = 5) -- this is where the
  Finset counting argument lives, fully kernel-proven.
* `all_nontrivial_zeros_in_box_on_critical_line`: the wired capstone which OBTAINS the divisor from
  `BlaschkeBox.zeta_blaschke_split_box`, so support/`d≥1` ARE kernel-derived, and carries only the
  honest Arb bundle (winding = 5, edge non-vanishing, interiority, integrability) as `hArb`. -/







end BoxLocalization


/-  Task 3 (parameterized RH-in-a-box): the GENERIC capstone + the regression instantiation.

    `conjecture1_proved = False`.  This composes the corner/count-generic counting core
    (`RHInBoxCore.rh_in_box_core`, Task 1) with the variable-ball parameterized argument-principle
    count (`RHInBoxAnalytic.zeta_count_eq_winding_generic`, Task 2) into the ONE generic theorem
    `RHInBox.rh_in_box_of_certificate`, instantiable on ANY finite box `[sigma0,sigma1]x[T0,T1]` with
    ANY Blaschke ball `(c, R)` and ANY on-line-zero count `N`.

    It then proves the regression `RHInBox.rh_in_box_10_35`: the generic theorem, instantiated at the
    ORIGINAL merged box's values `sigma0=2/5, sigma1=3/5, T0=10, T1=35, c=cB, R=13, N=5` with `T` the
    five known on-line zeros, reproduces the SAME conclusion as the merged capstone
    `BoxLocalization.all_nontrivial_zeros_in_box_on_critical_line`.

    `N` is a FREE VARIABLE in the generic theorem; the regression fixes it to 5.

    conjecture1_proved = False.  This VERIFIES RH inside a box for supplied Arb data; it is NOT a
    proof of the Riemann Hypothesis. -/

        -- Task 1: rh_in_box_core
    -- Task 2: zeta_count_eq_winding_generic + zeroFinset
    -- zeta_zero_iff_completed_zero bridge + merged capstone (for regression)
        -- cB / boxB for the regression instantiation

open Complex MeasureTheory Real
open scoped Topology

namespace RHInBox

/-! ## Part A0: O(N) on-line Finset construction from a sorted list.

    The per-box instantiations build their on-line Finset `T` from `N` critical-line points.
    Doing this with a Finset literal needs `N*(N-1)/2` pairwise-distinctness proofs (the O(N^2)
    block that dominates emitted-proof cost at large `N`).  These lemmas replace it: the emitted
    proof supplies only the O(N) consecutive chain `x1 < x2 < ... < xN`, and `line_toFinset_card`
    converts chain -> Nodup -> card = length ONCE, generically.  conjecture1_proved = False. -/

/-- The critical-line embedding `t ↦ 1/2 + t*I` is injective. -/
theorem lineEmbed_injective : Function.Injective (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
  intro a b h
  have h1 : (a : ℂ) * Complex.I = (b : ℂ) * Complex.I := by
    have := h
    simpa using congrArg (fun z => z - (1 / 2 : ℂ)) this
  have h2 : (a : ℂ) = (b : ℂ) := mul_right_cancel₀ Complex.I_ne_zero h1
  exact_mod_cast h2

/-- A strictly-increasing list of reals maps to a `Nodup` list on the critical line. -/
theorem line_map_nodup (xs : List ℝ) (h : xs.IsChain (· < ·)) :
    (xs.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).Nodup := by
  have hp : xs.Pairwise (· < ·) := List.isChain_iff_pairwise.mp h
  have hnd : xs.Nodup := hp.imp (fun {a b} hab => ne_of_lt hab)
  exact hnd.map lineEmbed_injective

/-- The on-line Finset built from a strictly-increasing list has `card = length`.  This is the
    O(N) replacement for the emitted pairwise-distinctness + insert-peeling card proof. -/
theorem line_toFinset_card (xs : List ℝ) (h : xs.IsChain (· < ·)) :
    (xs.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).toFinset.card = xs.length := by
  rw [List.toFinset_card_of_nodup (line_map_nodup xs h), List.length_map]

/-- Transport a pointwise property of the list's line points to the built Finset. -/
theorem line_toFinset_forall {P : ℂ → Prop} (xs : List ℝ)
    (hP : ∀ t ∈ xs, P ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) :
    ∀ z ∈ (xs.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).toFinset, P z := by
  intro z hz
  rw [List.mem_toFinset, List.mem_map] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  exact hP t ht

/-! ## Part A: the generic capstone. -/



/-! ## Part B: the regression instantiation on the original box `[2/5, 3/5] x [10, 35]`.

    We instantiate `rh_in_box_of_certificate` with the ORIGINAL merged box's parameters — corners
    `2/5, 3/5, 10, 35`, ball `(cB, 13)`, count `N = 5` — and supply the on-line Finset `T` as the
    five bridged on-line zeros from Stage 1 (`hLine`).  Geometry (`hRpos`/`hbox_ball`/`hs1`/
    `hsig`/`hT`) is discharged by `norm_num`/the merged `BlaschkeBox` facts.  The Arb bundle and
    winding value carry over verbatim from the merged `all_nontrivial_zeros_in_box_on_critical_line`
    input shape; the winding value `= 2*pi*I*5` supplies `hwind`, and `hcount : (5:Z) = T.card`
    holds because the five on-line zeros are distinct.

    The conclusion is DEFINITIONALLY the merged capstone's conclusion — this is the regression. -/



end RHInBox


/-  H11K_Turing.lean -- lane H11K: the Turing band template with SHARP pi pins, for WIDE bands.

    `TuringBand.band_count_eq` pins the band count with `3.14 < π < 3.1416`.  The upper pin
    `2 H1 + H2 - L3 + H4 + H5 < 2 * 3.14 * (N + 1)` then loses `2 (π - 3.14) N ≈ 0.0032 N` radians,
    which (with the K6a range `[-249/250, 249/250]` alone costing about 4 radians) caps a band at
    roughly 700 zeros.  A single band over `[31851/4, 11004]` holds 3541 zeros.  This file re-proves
    the same template with `3.141592 < π < 3.141593` (`Real.pi_gt_d6`, `Real.pi_lt_d6`); the RvM
    edge decomposition (`DiffractionCore.zero_count_band_edge_decomp`), the Blaschke split and the
    count-exhaustion core are reused unchanged.

      * `band_count_eq_sharp`, `turing_band_on_line_sharp` -- `TuringBand.band_count_eq` /
        `turing_band_on_line` with the sharp pins (proofs copied, constants changed);
      * `ValidS`, `stmt_of_validS` -- `BandGlue.BandData.Valid` / `stmt_of_valid` with the sharp
        pins; the conclusion is the band's canonical statement `d.Stmt σ0 σ1` (the same Prop,
        `TuringBand.BandStatement`, whatever the pins), so every other piece of `BandGlue` applies;
      * `validBS`, `validS_of_B` -- the decidable side conditions as ONE Boolean (as `Arb4.validB`);
      * `boxCert_of_parts_sharp` -- `Arb4.boxCert_of_parts` with `ValidS`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (H11K_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/


open Complex

section
namespace H11K
end H11K
open H11K





open BandGlue BandGlue.BandData




theorem solution {σ0 σ1 : ℝ} {d : BandData} (hV : ValidS σ0 σ1 d) : d.Stmt σ0 σ1 := by
  intro hLine hArbT
  obtain ⟨xsL, hlen, hchain, hbnd, hzeros⟩ := hLine
  obtain ⟨hnzb, hnzt, hnzl, hins, hAV2, hAHt, hAHb, hAG1, hAG2⟩ := hArbT
  have hre_line : ∀ (t : ℝ), (1 / 2 + (t : ℂ) * Complex.I).re = 1 / 2 := by
    intro t
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; norm_num
  have him_line : ∀ (t : ℝ), (1 / 2 + (t : ℂ) * Complex.I).im = t := by
    intro t
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; norm_num
  set T : Finset ℂ :=
    (xsL.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).toFinset with hTdef
  have hTcard : T.card = d.n := by
    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hlen]
  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t _ => hre_line t)
  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL
      (fun t ht => BoxLocalization.line_zeta_zero_of_completed (hzeros t ht))
  have hTbox : ∀ z ∈ T, (σ0 ≤ z.re ∧ z.re ≤ σ1) ∧ (d.T0 ≤ z.im ∧ z.im ≤ d.T1) := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL (fun t ht => ?_)
    exact ⟨⟨by rw [hre_line]; exact hV.hre_lo, by rw [hre_line]; exact hV.hre_hi⟩,
      by rw [him_line]; exact (hbnd t ht).1, by rw [him_line]; exact (hbnd t ht).2⟩
  have hcountN : ((d.n : ℕ) : ℤ) = (T.card : ℤ) := by rw [hTcard]
  exact turing_band_on_line_sharp σ0 σ1 d.T0 d.T1 hV.hT0 hV.hT hV.hs0 hV.hs2
    d.c d.R hV.hRpos d.n hV.hN1 d.L1 d.H1 d.L2 d.H2 d.L3 d.H3 d.L4 d.H4 d.L5 d.H5
    hV.hbox_ball d.hs1 hnzb hnzt hnzl hins hAV2 hAHt hAHb hAG1 hAG2 hV.hpinL hV.hpinH
    T hTline hTzero hTbox hcountN

-- Prove2me | solution 1 for H11K.band_count_eq_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:14:23.626599+00:00
-- url     : https://prove2.me/submissions/562a8994-0f35-45ec-8587-9eadf2562854

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
import Theorems.Thm_DiffractionCore_zero_count_band_edge_decomp

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


theorem solution
    (T0 T1 : ℝ) (hT0 : 0 < T0) (hT : T0 ≤ T1)
    (c : ℂ) (R : ℝ) (N : ℕ) (hN1 : 1 ≤ N)
    (L1 H1 L2 H2 L3 H3 L4 H4 L5 H5 : ℝ)
    (hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ T0 < ρ.im ∧ ρ.im < T1)
    (hAV2 : DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc L1 H1)
    (hAHt : DiffractionCore.argChangeHoriz riemannZeta T1 2 (-1) ∈ Set.Icc L2 H2)
    (hAHb : DiffractionCore.argChangeHoriz riemannZeta T0 2 (-1) ∈ Set.Icc L3 H3)
    (hAG1 : DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1 ∈ Set.Icc L4 H4)
    (hAG2 : DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 ∈ Set.Icc L5 H5)
    (hpinL : 2 * 3.141593 * ((N : ℝ) - 1) < 2 * L1 + L2 - H3 + L4 + L5)
    (hpinH : 2 * H1 + H2 - L3 + H4 + H5 < 2 * 3.141592 * ((N : ℝ) + 1)) :
    (∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ) = (N : ℤ) := by
  have hdecomp := DiffractionCore.zero_count_band_edge_decomp T0 T1 hT0 hT c R
    hbox_ball hs1 hnzb hnzt hnzl hins
  set Sz : ℤ := ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
    (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ with hSz
  have hSreal : (2 : ℝ) * Real.pi * (Sz : ℝ)
      = 2 * DiffractionCore.argChangeVert riemannZeta 2 T0 T1
        + DiffractionCore.argChangeHoriz riemannZeta T1 2 (-1)
        - DiffractionCore.argChangeHoriz riemannZeta T0 2 (-1)
        + DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1
        + DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 := by
    have hcast : ((Sz : ℤ) : ℝ) = ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℤ) : ℝ) := by
      rw [hSz]; push_cast; ring
    rw [hcast]; exact hdecomp
  have hpigt : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpilt : Real.pi < 3.141593 := Real.pi_lt_d6
  have hlo : 2 * Real.pi * ((N : ℝ) - 1) < 2 * Real.pi * (Sz : ℝ) := by
    have h1 : 2 * Real.pi * ((N : ℝ) - 1) ≤ 2 * 3.141593 * ((N : ℝ) - 1) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) - 1 := by
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
        linarith
      nlinarith [hN0, hpilt]
    have h2 : 2 * L1 + L2 - H3 + L4 + L5 ≤ 2 * Real.pi * (Sz : ℝ) := by
      rw [hSreal]
      obtain ⟨l1, h1'⟩ := hAV2; obtain ⟨l2, h2'⟩ := hAHt; obtain ⟨l3, h3'⟩ := hAHb
      obtain ⟨l4, h4'⟩ := hAG1; obtain ⟨l5, h5'⟩ := hAG2
      linarith
    linarith
  have hhi : 2 * Real.pi * (Sz : ℝ) < 2 * Real.pi * ((N : ℝ) + 1) := by
    have h1 : 2 * 3.141592 * ((N : ℝ) + 1) ≤ 2 * Real.pi * ((N : ℝ) + 1) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      nlinarith [hN0, hpigt]
    have h2 : 2 * Real.pi * (Sz : ℝ) ≤ 2 * H1 + H2 - L3 + H4 + H5 := by
      rw [hSreal]
      obtain ⟨l1, h1'⟩ := hAV2; obtain ⟨l2, h2'⟩ := hAHt; obtain ⟨l3, h3'⟩ := hAHb
      obtain ⟨l4, h4'⟩ := hAG1; obtain ⟨l5, h5'⟩ := hAG2
      linarith
    linarith
  have hpipos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hltN : ((N : ℝ) - 1) < (Sz : ℝ) :=
    lt_of_mul_lt_mul_left (by linarith [hlo]) (le_of_lt hpipos)
  have hgtN : (Sz : ℝ) < ((N : ℝ) + 1) :=
    lt_of_mul_lt_mul_left (by linarith [hhi]) (le_of_lt hpipos)
  have hzlt : (N : ℤ) - 1 < Sz := by exact_mod_cast hltN
  have hzgt : Sz < (N : ℤ) + 1 := by exact_mod_cast hgtN
  omega

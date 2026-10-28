-- Prove2me | solution 1 for H11K.validS_of_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:00:42.06952+00:00
-- url     : https://prove2.me/submissions/4ab3adce-470e-4989-83a6-0a01052d76ea

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
import Theorems.Thm_H1000Line_box_ball_of_sqrt
namespace BandGlue
end BandGlue
namespace BandGlue.BandData
end BandGlue.BandData

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






theorem solution (d : BandData) (t0 t1 cim q : ℝ) (hT0v : d.T0 = t0) (hT1v : d.T1 = t1)
    (hcv : d.c = (⟨1 / 2, cim⟩ : ℂ)) (hRv : d.R = Real.sqrt q) (hn : 1 ≤ d.n)
    (ht0 : 0 < t0) (ht : t0 ≤ t1) (hq : 0 < q) (h0 : t0 ≤ cim) (h1 : cim ≤ t1)
    (ha : 9 / 4 + (cim - t0) ^ 2 < q) (hb : 9 / 4 + (t1 - cim) ^ 2 < q)
    (hpinL : 2 * 3.141593 * ((d.n : ℝ) - 1) < 2 * d.L1 + d.L2 - d.H3 + d.L4 + d.L5)
    (hpinH : 2 * d.H1 + d.H2 - d.L3 + d.H4 + d.H5 < 2 * 3.141592 * ((d.n : ℝ) + 1)) :
    ValidS (1 / 4000000) (3999999 / 4000000) d where
  hT0 := by rw [hT0v]; exact ht0
  hT := by rw [hT0v, hT1v]; exact ht
  hs0 := by norm_num
  hs2 := by norm_num
  hre_lo := by norm_num
  hre_hi := by norm_num
  hRpos := by rw [hRv]; exact Real.sqrt_pos.mpr hq
  hN1 := hn
  hbox_ball := by
    intro ρ hre him
    rw [hcv, hRv]
    rw [hT0v, hT1v] at him
    exact H1000Line.box_ball_of_sqrt h0 h1 ha hb ρ hre him
  hpinL := hpinL
  hpinH := hpinH

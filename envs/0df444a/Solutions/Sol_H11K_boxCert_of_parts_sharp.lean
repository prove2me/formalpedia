-- Prove2me | solution 1 for H11K.boxCert_of_parts_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:26:04.497064+00:00
-- url     : https://prove2.me/submissions/1401f5fb-b368-477f-8c37-e0583ea20b87

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
import Theorems.Thm_ArgGammaR_argChangeVert_gammaR_neg_one_eq
import Theorems.Thm_ArgGammaR_argChangeVert_gammaR_two_eq
import Theorems.Thm_ArgZetaTwo_argChangeVert_zeta_two_eq
import Theorems.Thm_ArgZetaTwo_log_pi_sq_div_six_lt
import Theorems.Thm_ArgZetaTwo_log_zeta_two_eq
import Theorems.Thm_ArgZetaTwo_norm_primeLog_le
import Theorems.Thm_ArgZetaTwo_primeLog_two
import Theorems.Thm_EdgeClearGlue_hins_of_slabClear
import Theorems.Thm_H11K_stmt_of_validS
import Theorems.Thm_RSDesignTheta_lam_bracket
import Theorems.Thm_ThetaConverge_imLnVal_cauchy
import Theorems.Thm_ZetaZeroConfinement_zeta_zero_iff_completed_zero_of_im_ne
namespace Arb4
end Arb4
namespace Arb4.Q
end Arb4.Q
namespace BandGlue
end BandGlue
namespace BandGlue.BandData
end BandGlue.BandData
namespace RSDesignTheta
end RSDesignTheta
namespace ThetaGap
end ThetaGap
/- CONFINEMENT (kernel): every nontrivial zeta zero up to height T lies in the band [a, 1-a].

   This is the "confinement" half of the "all zeros up to height T are on the line" project:
   box-localization (all zeros IN a box on the line, PR #312) + confinement (all zeros ARE in the
   box, this file).  We prove the confinement:

     `zero_in_band` :  a nontrivial zero `ρ` (`ζ ρ = 0`, `0 < ρ.im ≤ T`) with `a ≤ dlvpRateC/log T`
                       satisfies  `a ≤ ρ.re ≤ 1 - a`.

   Both edges come from the SELF-CONTAINED effective de la Vallée Poussin zero-free region
   `ZeroFreeBridge.riemannZeta_ne_zero_region` (PR #318 -- no multiplicity input, β≥3/4 discharged
   internally): `ζ(β+iγ) ≠ 0` for `|γ| ≥ 55/16` and `β > 1 - dlvpRateC/log|γ|`.

   - RIGHT edge `ρ.re ≤ 1-a`:  contrapositive of the region at `ρ` gives `ρ.re ≤ 1 - dlvpRateC/log|γ|`,
     and `dlvpRateC/log|γ| ≥ dlvpRateC/log T ≥ a` (log monotone, `|γ| = ρ.im ≤ T`; `dlvpRateC > 0`).
   - LEFT edge `a ≤ ρ.re`:  reflect through the functional equation.  `ζ ρ = 0` ⟹ `Λ ρ = 0`
     (unconditional strip bridge: `ρ.im ≠ 0` ⟹ `Gammaℝ ρ ≠ 0`) ⟹ `Λ (1-ρ) = 0`
     (`completedRiemannZeta_one_sub`) ⟹ `ζ (1-ρ) = 0` (strip bridge again, `(1-ρ).im = -ρ.im ≠ 0`).
     The reflected zero has real part `1-ρ.re`, height `-ρ.im`, `|-ρ.im| = |ρ.im| ≥ 55/16`.  The
     region contrapositive on it gives `1-ρ.re ≤ 1 - dlvpRateC/log|γ| ≤ 1 - a`, i.e. `ρ.re ≥ a`.

   RESIDUAL (documented, honest -- a genuine Mathlib gap, NOT a fake).  Mathlib has no "no zeta
   zeros with `|Im| < 14`" fact (the first nontrivial zero is at height ~14.13 > 55/16 ~ 3.44), so
   the region's height-floor hypothesis `55/16 ≤ |ρ.im|` is carried as an ADDED hypothesis `hγ` on
   `zero_in_band`.  It is a small classical fact, discharged at the concrete T=100 instantiation
   from the on-line sweep (all 29 zeros up to 100 have height ≥ 14 > 55/16).  No multiplicity input,
   no `β ≥ 3/4` casework, no `0 < ρ.re` strip hypothesis (the FE strip bridge here is unconditional
   for `ρ.im ≠ 0`).

   conjecture1_proved = False (a kernel-verified reduction of confinement to the effective dVP
   region + the functional equation, NOT a proof of RH).
-/



open Complex

namespace ZetaZeroConfinement



/-- **The functional-equation reflection of an off-real zeta zero.**  `ζ ρ = 0` with `ρ.im ≠ 0`
    forces `ζ (1 - ρ) = 0`. -/
theorem zeta_zero_reflect {ρ : ℂ} (him : ρ.im ≠ 0) (hzero : riemannZeta ρ = 0) :
    riemannZeta (1 - ρ) = 0 := by
  have hΛ : completedRiemannZeta ρ = 0 := (zeta_zero_iff_completed_zero_of_im_ne him).1 hzero
  have hΛ' : completedRiemannZeta (1 - ρ) = 0 := by
    rw [completedRiemannZeta_one_sub]; exact hΛ
  have him' : (1 - ρ).im ≠ 0 := by
    rw [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero]; exact him
  exact (zeta_zero_iff_completed_zero_of_im_ne him').2 hΛ'



/-- **Critical-strip location of a nontrivial (off-real) zeta zero.**  `ζ ρ = 0` with `ρ.im ≠ 0`
    forces `0 < ρ.re ∧ ρ.re < 1`.  `Re < 1` is `riemannZeta_ne_zero_of_one_le_re` directly; `0 < Re`
    is the same lemma applied to the functional-equation reflection `1 - ρ` (`zeta_zero_reflect`),
    whose real part `1 - ρ.re ≥ 1` when `ρ.re ≤ 0`.  Off-real is essential — the trivial zeros lie
    on the real axis at the negative even integers (`Re ≤ 0`). -/
theorem zeta_zero_re_mem_strip {ρ : ℂ} (him : ρ.im ≠ 0) (hz : riemannZeta ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    have hrefl : riemannZeta (1 - ρ) = 0 := zeta_zero_reflect him hz
    have hge : (1 : ℝ) ≤ (1 - ρ).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    exact riemannZeta_ne_zero_of_one_le_re hge hrefl
  · by_contra h
    push_neg at h
    exact riemannZeta_ne_zero_of_one_le_re h hz



end ZetaZeroConfinement


/-  ArgGammaR.lean -- brick K6b of the ANDURIL Arb discharge (with the T6 bridge it needs)
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, inventory row H2f, bricks K6b and T6).

    THE BINDERS IT DISCHARGES.  Conjuncts 8 and 9 of the `hArbT` binder of every emitted Turing
    band (`TuringBand.BandStatement`, `BandGlue.BandData.EnclHyp`) are

        hAG1 : DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1 ∈ Set.Icc L4 H4,
        hAG2 : DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 ∈ Set.Icc L5 H5,

    the argument changes of the archimedean factor `Γℝ(s) = π^{-s/2} Γ(s/2)` up the two vertical
    edges of the RvM rectangle.  The emitted bands feed them 1e-12-wide Arb enclosures.  This file
    proves them HYPOTHESIS-FREE for every `0 ≤ T0`, `0 ≤ T1`, with explicit elementary endpoints
    (logs and arctans), in the exact binder form:

        argChangeVert Γℝ 2 T0 T1    ∈ [S2 T1 - S2 T0 - e2 T1,  S2 T1 - S2 T0 + e2 T0]    (`hAG2_closed`)
        argChangeVert Γℝ (-1) T0 T1 ∈ [Sm1 T1 - Sm1 T0 - em1 T1, Sm1 T1 - Sm1 T0 + em1 T0] (`hAG1_closed`)

        S2 T  = (1/2) arctan (T/2) + (T/4) log (1 + T²/4) - T/2 - (T/2) log π,   e2 T  = T/(2(4 + T²)),
        Sm1 T = (T/4) log (1/4 + T²/4) + arctan T - T/2 - (T/2) log π,          em1 T = T/(2(1 + T²)),

    plus the sharper `hAG2_mem` / `hAG1_mem` at any Stirling base index `n0` (error
    `y/(4((x+n0)² + y²))` at each edge, `y = T/2`), for the lowest bands.

    THE T6 BRIDGE (`integral_half_re_digamma`).  `RSTheta.lam_bracket` brackets the GAUSS BRANCH
    `Λ(x, y) = lim_n imLnVal x y n` (`gaussLam`), a limit of arctan sums.  The binders are integrals
    of `logDeriv Γℝ`.  The bridge identifies them: for `x > 0` and all `a`, `b`,

        ∫_a^b (1/2) Re ψ(x + i y/2) dy = Λ(x, b/2) - Λ(x, a/2),

    proved WITHOUT any locally-uniform-convergence machinery:
      * finite FTC: `d/dy imLnVal x (y/2) n = (1/2)(log n - Σ_{k≤n} (x+k)/((x+k)² + (y/2)²))`;
      * `ZeroFreeBridge.digamma_shift`: Re ψ(z) = [that sum] + Re(ψ(z + n + 1) - log n);
      * the remainder is at most `(x + 2 + |y|/2)/(2n)` (Binet bound
        `ZeroFreeBridge.norm_digamma_sub_log_le` at `Re ≥ 2` plus `log u ≤ u - 1`), so its
        integral is `O(1/n)`, and uniqueness of limits closes the identity.
    Then `logDeriv Γℝ s = -(log π)/2 + (1/2) ψ(s/2)` gives the σ = 2 edge at `x = 1`, and at σ = -1
    the shift `ψ(z) = ψ(z+1) - 1/z` (`z = -1/2 + i y/2`) gives `x = 1/2` plus the elementary
    `∫ 1/(1 + y²) = arctan T1 - arctan T0`.

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  Elementary enclosures of the Γ-factor edges of a finite zero
    count; nothing here bears on the Riemann Hypothesis. -/




open Complex Filter Topology
open ThetaGap RSDesignTheta

namespace ArgGammaR

/-! ## 1. The Gauss-branch limit `Λ(x, y)` -/



theorem tendsto_gaussLam {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Tendsto (imLnVal x y) atTop (𝓝 (gaussLam x y)) :=
  (ThetaConverge.imLnVal_cauchy x y hx).tendsto_limUnder





/-- `lamC - lamE ≤ Λ ≤ lamC` (the height-uniform Stirling bracket, `RSTheta.lam_bracket`). -/
theorem gaussLam_mem {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (n0 : ℕ) :
    lamC x y n0 - lamE x y n0 ≤ gaussLam x y ∧ gaussLam x y ≤ lamC x y n0 :=
  lam_bracket x y hx hy n0 _ (tendsto_gaussLam hx y)

/-! ## 2. The T6 bridge: `∫ (1/2) Re ψ(x + i y/2) dy = Λ(x, b/2) - Λ(x, a/2)` -/





















/-! ## 3. `logDeriv Γℝ` on the two vertical edges -/

















/-! ## 4. The two edge identities -/





/-! ## 5. The hypothesis-free enclosures (K6b) -/





/-- **K6b, σ = 2, any base index `n0`** (every `0 ≤ T0`, `0 ≤ T1`), exact `hAG2` binder form. -/
theorem hAG2_mem (n0 : ℕ) {T0 T1 : ℝ} (h0 : 0 ≤ T0) (h1 : 0 ≤ T1) :
    DiffractionCore.argChangeVert Gammaℝ 2 T0 T1
      ∈ Set.Icc (phase2 n0 T1 - lamE 1 (T1 / 2) n0 - phase2 n0 T0)
          (phase2 n0 T1 - phase2 n0 T0 + lamE 1 (T0 / 2) n0) := by
  rw [argChangeVert_gammaR_two_eq]
  have hb1 := gaussLam_mem (x := 1) (y := T1 / 2) (by norm_num) (by linarith) n0
  have hb0 := gaussLam_mem (x := 1) (y := T0 / 2) (by norm_num) (by linarith) n0
  unfold phase2
  constructor <;> linarith [hb1.1, hb1.2, hb0.1, hb0.2]

/-- **K6b, σ = -1, any base index `n0`** (every `0 ≤ T0`, `0 ≤ T1`), exact `hAG1` binder form. -/
theorem hAG1_mem (n0 : ℕ) {T0 T1 : ℝ} (h0 : 0 ≤ T0) (h1 : 0 ≤ T1) :
    DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1
      ∈ Set.Icc (phaseM1 n0 T1 - lamE (1 / 2) (T1 / 2) n0 - phaseM1 n0 T0)
          (phaseM1 n0 T1 - phaseM1 n0 T0 + lamE (1 / 2) (T0 / 2) n0) := by
  rw [argChangeVert_gammaR_neg_one_eq]
  have hb1 := gaussLam_mem (x := 1 / 2) (y := T1 / 2) (by norm_num) (by linarith) n0
  have hb0 := gaussLam_mem (x := 1 / 2) (y := T0 / 2) (by norm_num) (by linarith) n0
  unfold phaseM1
  constructor <;> linarith [hb1.1, hb1.2, hb0.1, hb0.2]









theorem phase2_zero (T : ℝ) : phase2 0 T = S2 T := by
  unfold phase2 lamC S2 FA fA
  simp only [Nat.cast_zero, add_zero, zero_add, Finset.range_one, Finset.sum_singleton, div_one]
  have h : (1 : ℝ) ^ 2 + (T / 2) ^ 2 = 1 + T ^ 2 / 4 := by ring
  rw [h]
  ring

theorem phaseM1_zero (T : ℝ) : phaseM1 0 T = Sm1 T := by
  unfold phaseM1 lamC Sm1 FA fA
  simp only [Nat.cast_zero, add_zero, zero_add, Finset.range_one, Finset.sum_singleton]
  have h : (1 / 2 : ℝ) ^ 2 + (T / 2) ^ 2 = 1 / 4 + T ^ 2 / 4 := by ring
  rw [h]
  ring

theorem lamE_one_zero (T : ℝ) : lamE 1 (T / 2) 0 = e2 T := by
  unfold lamE e2
  simp only [Nat.cast_zero, add_zero]
  rw [div_div]
  congr 1
  ring

theorem lamE_half_zero (T : ℝ) : lamE (1 / 2) (T / 2) 0 = em1 T := by
  unfold lamE em1
  simp only [Nat.cast_zero, add_zero]
  rw [div_div]
  congr 1
  ring

/-- **K6b, σ = 2, closed form, exact `hAG2` binder form** (hypothesis-free, every `0 ≤ T0`,
    `0 ≤ T1`): `argChangeVert Γℝ 2 T0 T1 ∈ [S2 T1 - S2 T0 - e2 T1, S2 T1 - S2 T0 + e2 T0]`. -/
theorem hAG2_closed {T0 T1 : ℝ} (h0 : 0 ≤ T0) (h1 : 0 ≤ T1) :
    DiffractionCore.argChangeVert Gammaℝ 2 T0 T1
      ∈ Set.Icc (S2 T1 - S2 T0 - e2 T1) (S2 T1 - S2 T0 + e2 T0) := by
  have h := hAG2_mem 0 h0 h1
  rw [phase2_zero, phase2_zero, lamE_one_zero, lamE_one_zero] at h
  exact ⟨by linarith [h.1], h.2⟩

/-- **K6b, σ = -1, closed form, exact `hAG1` binder form** (hypothesis-free, every `0 ≤ T0`,
    `0 ≤ T1`): `argChangeVert Γℝ (-1) T0 T1 ∈ [Sm1 T1 - Sm1 T0 - em1 T1, Sm1 T1 - Sm1 T0 + em1 T0]`. -/
theorem hAG1_closed {T0 T1 : ℝ} (h0 : 0 ≤ T0) (h1 : 0 ≤ T1) :
    DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1
      ∈ Set.Icc (Sm1 T1 - Sm1 T0 - em1 T1) (Sm1 T1 - Sm1 T0 + em1 T0) := by
  have h := hAG1_mem 0 h0 h1
  rw [phaseM1_zero, phaseM1_zero, lamE_half_zero, lamE_half_zero] at h
  exact ⟨by linarith [h.1], h.2⟩

/-- `hAG2` for any enclosure `[L5, H5]` containing the closed-form bracket (the shape a band
    emitter discharges with rational bounds on the logs and arctans at its two edges). -/
theorem hAG2_of_bounds {T0 T1 L5 H5 : ℝ} (h0 : 0 ≤ T0) (h1 : 0 ≤ T1)
    (hL : L5 ≤ S2 T1 - S2 T0 - e2 T1) (hH : S2 T1 - S2 T0 + e2 T0 ≤ H5) :
    DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 ∈ Set.Icc L5 H5 := by
  have h := hAG2_closed h0 h1
  exact ⟨le_trans hL h.1, le_trans h.2 hH⟩

/-- `hAG1` for any enclosure `[L4, H4]` containing the closed-form bracket. -/
theorem hAG1_of_bounds {T0 T1 L4 H4 : ℝ} (h0 : 0 ≤ T0) (h1 : 0 ≤ T1)
    (hL : L4 ≤ Sm1 T1 - Sm1 T0 - em1 T1) (hH : Sm1 T1 - Sm1 T0 + em1 T0 ≤ H4) :
    DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1 ∈ Set.Icc L4 H4 := by
  have h := hAG1_closed h0 h1
  exact ⟨le_trans hL h.1, le_trans h.2 hH⟩

/-! ## 6. Rational instantiation helpers (for band emitters) -/









end ArgGammaR


/-  ArgZetaTwo.lean -- brick K6a of the ANDURIL Arb discharge
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, inventory row H2d, brick K6a).

    THE BINDER IT DISCHARGES.  Conjunct 5 of the `hArbT` binder of every emitted Turing band
    (`TuringBand.BandStatement`, `BandGlue.BandData.EnclHyp`) is

        hAV2 : DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc L1 H1,

    the argument change of ζ up the line `Re s = 2` between the band edges.  The emitted bands feed
    it a 1e-12-wide Arb enclosure.  This file proves a GENERIC enclosure, valid for every `T0`,
    `T1` and hence for all 10,379 bands of the h280000 ladder at once:

        argChangeVert riemannZeta 2 T0 T1 ∈ [-249/250, 249/250]         (`hAV2_generic`)

    because `|arg ζ(2 + i t)| ≤ log ζ(2) = log (π²/6) < 0.498` for every real `t`.

    HOW.
      * `argChangeVert_zeta_two_eq`: the argument change IS a difference of principal arguments,
            argChangeVert ζ 2 T0 T1 = arg ζ(2 + i T1) - arg ζ(2 + i T0),
        by the fundamental theorem of calculus for `y ↦ log ζ(2 + i y)` (principal `Complex.log`),
        legitimate because `ζ(2 + i y)` stays in the right half-plane.
      * `arg_zeta_eq_im_primeLog`, `abs_arg_zeta_two_le`: on `Re s = 2`, ζ(s) = exp L(s) with
        L(s) = Σ_p -log(1 - p^{-s}) (Mathlib's `riemannZeta_eulerProduct_exp_log`), and
        ‖L(s)‖ ≤ Σ_p -log(1 - p^{-2}) =: G termwise (Taylor series of `-log(1 - z)` dominated
        by that of `-log(1 - ‖z‖)`).  Since G < π, `Complex.log (exp L) = L`, so
        arg ζ(s) = Im L(s) ∈ [-G, G]; since G < π/2, Re ζ(s) > 0.
      * `exp_primeSum`: exp G = ζ(2) = π²/6 (the same Euler product at the real point 2), so
        G = log (π²/6); `log_pi_sq_div_six_lt`: log (π²/6) < 249/500 from π < 3.1416 and the
        degree-6 Taylor lower bound of `exp`.

    This is the "Λ(n) series at σ = 2" bound of the memo: mathematically G = Σ_n Λ(n)/(n² log n) =
    log ζ(2); the formal route here is the prime Euler product, not the Λ(n) series itself.
    (Not formalized, for orientation only: by Kronecker's theorem the supremum of |arg ζ(2+it)| is
    Σ_p arcsin(p⁻²) ≈ 0.455, so the constant is within 10 percent of optimal.)

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  A height-uniform bound on one edge of a finite zero count; nothing
    here bears on the Riemann Hypothesis. -/



open Complex

namespace ArgZetaTwo

/-! ## 1. The logarithm of the Euler product -/



/-- The Euler product in exponential form (Mathlib). -/
theorem exp_primeLog {s : ℂ} (hs : 1 < s.re) : Complex.exp (primeLog s) = riemannZeta s :=
  riemannZeta_eulerProduct_exp_log hs







/-! ## 2. The real prime sum `G = Σ_p -log(1 - p^{-2})` -/



















/-- `exp G = π²/6`: the Euler product at the real point `2`. -/
theorem exp_primeSum : Real.exp primeSum = Real.pi ^ 2 / 6 := by
  have h := exp_primeLog (s := 2) (by norm_num)
  rw [primeLog_two, riemannZeta_two, ← Complex.ofReal_exp] at h
  exact_mod_cast h

/-- `G = log (π²/6) = log ζ(2)`. -/
theorem primeSum_eq : primeSum = Real.log (Real.pi ^ 2 / 6) := by
  rw [← exp_primeSum, Real.log_exp]







/-! ## 3. `|arg ζ(2 + i t)| ≤ G` -/







/-- `arg ζ(2 + i t) = Im L(2 + i t)`. -/
theorem arg_zeta_eq_im_primeLog (t : ℝ) :
    Complex.arg (riemannZeta ((2 : ℂ) + (t : ℂ) * I)) = (primeLog ((2 : ℂ) + (t : ℂ) * I)).im := by
  rw [← Complex.log_im, log_zeta_two_eq]

/-- **`|arg ζ(2 + i t)| ≤ log ζ(2)`** for every real `t`. -/
theorem abs_arg_zeta_two_le (t : ℝ) :
    |Complex.arg (riemannZeta ((2 : ℂ) + (t : ℂ) * I))| ≤ Real.log (Real.pi ^ 2 / 6) := by
  rw [arg_zeta_eq_im_primeLog, ← primeSum_eq]
  exact le_trans (Complex.abs_im_le_norm _) (norm_primeLog_le t)





/-! ## 4. The argument change up `Re s = 2` -/



/-- `|argChangeVert ζ 2 T0 T1| ≤ 2 log ζ(2)` for every `T0`, `T1`. -/
theorem abs_argChangeVert_zeta_two_le (T0 T1 : ℝ) :
    |DiffractionCore.argChangeVert riemannZeta 2 T0 T1| ≤ 2 * Real.log (Real.pi ^ 2 / 6) := by
  rw [argChangeVert_zeta_two_eq]
  have h1 := abs_arg_zeta_two_le T1
  have h0 := abs_arg_zeta_two_le T0
  rw [abs_le] at h0 h1 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

/-- **K6a in the exact `hAV2` binder form** (generic: every band, every height):
    `argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc (-(249/250)) (249/250)`. -/
theorem hAV2_generic (T0 T1 : ℝ) :
    DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc (-(249 / 250 : ℝ)) (249 / 250) := by
  have h := abs_argChangeVert_zeta_two_le T0 T1
  have hl := log_pi_sq_div_six_lt
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `hAV2` for any enclosure `[L1, H1] ⊇ [-249/250, 249/250]`. -/
theorem hAV2_of_le {T0 T1 L1 H1 : ℝ} (hL : L1 ≤ -(249 / 250)) (hH : 249 / 250 ≤ H1) :
    DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc L1 H1 := by
  have h := hAV2_generic T0 T1
  exact ⟨le_trans hL h.1, le_trans h.2 hH⟩

end ArgZetaTwo


/-  EdgeClearGlue.lean -- brick K1 of the ANDURIL Arb discharge
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 1.3: `hArbT_nonvanishing_of_edge_clear`).

    Every emitted Turing band `RHInBoxT_*.rh_in_box_*` states the canonical
    `TuringBand.BandStatement` and takes an Arb binder `hArbT` with nine conjuncts.  The first four
    are non-vanishing and confinement facts about the RvM rectangle `[-1, 2] x [T0, T1]` and the
    Blaschke ball `ball c R` that covers it:

      hnzb : ∀ x ∈ [-1, 2], ζ(x + T0 i) ≠ 0                      (H2a, bottom edge)
      hnzt : ∀ x ∈ [-1, 2], ζ(x + T1 i) ≠ 0                      (H2a, top edge)
      hnzl : ∀ y ∈ [T0, T1], ζ(-1 + y i) ≠ 0                     (H2b, left edge)
      hins : every zero of ζ in `ball c R` lies in (-1, 2) x (T0, T1)   (H2c, confinement)

    This file derives all four from
      * `ZetaZeroConfinement.zeta_zero_re_mem_strip`: an off-real zero of ζ has 0 < Re < 1;
      * the ball geometry: three rational/sqrt inequalities about c, R, T0, T1 (decidable per band);
      * two EDGE-CLEARANCE facts, the memo's E(T0, δ0) and E(T1, δ1), as zero-free SLABS on the
        OUTER side of each edge: `SlabClear (T0 - δ0) T0` and `SlabClear T1 (T1 + δ1)`, where
        `SlabClear a b` says ζ has no zero with 0 < Re < 1 and a ≤ Im ≤ b.

    H2b needs no input at all: `hnzl_discharged` proves the conjunct for EVERY `T0`, `T1`, with no
    hypotheses (off the real axis by the strip theorem; at y = 0 by ζ(-1) = -1/12).  That removes
    one binder from each of the 10,379 bands of the h280000 ladder.

    What remains numerical after this file: two one-sided slab facts per band, about the open strip
    0 < Re < 1 only.  WHY ONE-SIDED, AND HOW TALL (measured on the h280000 ladder with the float
    zero list at grid 0.01, the tight cases refined with mpmath; untrusted numerics, design only):
      * ONE-SIDED: at about 2,831 band edges a zero lies on the INNER side of the edge closer than
        the ball cap (as close as the grid resolves), so even a two-sided window of half-height
        equal to the cap would be false there.  Inner-side zeros are counted by the band; only
        the outer side must be clear, and that is all `hins` needs.
      * TALL ENOUGH, NOT TOO TALL: the slab must reach past the ball cap (δ ≥ cap; caps are 0.0574
        to 0.0922) and must stop before the nearest zero beyond the edge.  The margin between the
        two is as small as 4.3e-5 (top edge 154974: cap 0.092160, zero at 154974.092203).  So δ
        must be the band's own cap rounded up finely (emit_band_glue.py uses 1e-6); a round
        δ = 1/10 would make the slab hypothesis false at about 385 of the 10,379 bands.

    Trust: no hypotheses beyond those named in each statement; axioms
    [propext, Classical.choice, Quot.sound] (see AxiomGuardBandGlue.lean).  No `sorry`.

    conjecture1_proved = False.  This is glue for a finite verification up to a fixed height; it
    says nothing about the Riemann Hypothesis. -/




open Complex

namespace EdgeClearGlue

/-! ## Zeta off the critical strip -/

/-- ζ has no zero with `Re s ≤ 0` off the real axis (the strip theorem, contrapositive). -/
theorem riemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hre : s.re ≤ 0) (him : s.im ≠ 0) :
    riemannZeta s ≠ 0 := fun hz =>
  absurd (ZetaZeroConfinement.zeta_zero_re_mem_strip him hz).1 (not_lt.mpr hre)

/-- `ζ(-1) = -1/12`, via `riemannZeta_neg_nat_eq_bernoulli` at `k = 1` and `bernoulli 2 = 1/6`. -/
theorem riemannZeta_neg_one : riemannZeta (-1) = -1 / 12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  simp only [Nat.cast_one, pow_one, Nat.reduceAdd] at h
  rw [h, bernoulli_two]
  norm_num

/-- `ζ(-1) ≠ 0`. -/
theorem riemannZeta_neg_one_ne_zero : riemannZeta (-1) ≠ 0 := by
  rw [riemannZeta_neg_one]; norm_num

/-- **H2b, pointwise**: `ζ(-1 + y i) ≠ 0` for EVERY real `y`. -/
theorem riemannZeta_neg_one_add_mul_I_ne_zero (y : ℝ) :
    riemannZeta (((-1 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
  by_cases hy : y = 0
  · subst hy
    have h : (((-1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = -1 := by push_cast; ring
    rw [h]; exact riemannZeta_neg_one_ne_zero
  · apply riemannZeta_ne_zero_of_re_nonpos
    · simp
    · simpa using hy

/-- **H2b DISCHARGED** (the `hnzl` conjunct of every Turing band, verbatim shape): no
    hypotheses, for all `T0`, `T1`. -/
theorem hnzl_discharged (T0 T1 : ℝ) :
    ∀ y ∈ Set.uIcc T0 T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0 :=
  fun y _ => riemannZeta_neg_one_add_mul_I_ne_zero y

/-! ## Edge clearance: zero-free slabs -/





/-- **H2a from a slab containing the edge height**: the whole horizontal edge `[-1, 2] + T i` is
    zero-free (in fact every `x`, not only `x ∈ [-1, 2]`), given `T ≠ 0`. -/
theorem hnz_edge_of_slabClear {T a b : ℝ} (hT : T ≠ 0) (ha : a ≤ T) (hb : T ≤ b)
    (hE : SlabClear a b) :
    ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T : ℂ) * I) ≠ 0 := by
  intro x _ hz
  have him : ((x : ℂ) + (T : ℂ) * I).im ≠ 0 := by simpa using hT
  obtain ⟨h0, h1⟩ := ZetaZeroConfinement.zeta_zero_re_mem_strip him hz
  have hre : ((x : ℂ) + (T : ℂ) * I).re = x := by simp
  rw [hre] at h0 h1
  exact hE x T h0 h1 ha hb hz

/-! ## Confinement of the Blaschke-ball zeros -/







/-- **K1: `hArbT_nonvanishing_of_edge_clear`.**  The four non-vanishing / confinement conjuncts
    of a Turing band's `hArbT` binder, in the verbatim shape of `TuringBand.BandStatement`, from
    the two edge-clearance slabs (below `T0`, above `T1`) and the ball geometry.  `hnzl` needs
    neither. -/
theorem hArbT_nonvanishing_of_edge_clear {T0 T1 δ0 δ1 : ℝ} {c : ℂ} {R : ℝ}
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hT0 : T0 ≠ 0) (hT1 : T1 ≠ 0) (hδ0 : 0 ≤ δ0) (hδ1 : 0 ≤ δ1)
    (hpos : 0 ≤ c.im - R) (hlo : T0 - δ0 ≤ c.im - R) (hhi : c.im + R ≤ T1 + δ1)
    (hE0 : SlabClear (T0 - δ0) T0) (hE1 : SlabClear T1 (T1 + δ1)) :
    (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0) ∧
    (∀ y ∈ Set.uIcc T0 T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
    (∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ T0 < ρ.im ∧ ρ.im < T1) :=
  ⟨hnz_edge_of_slabClear hT0 (by linarith) le_rfl hE0,
    hnz_edge_of_slabClear hT1 le_rfl (by linarith) hE1, hnzl_discharged T0 T1,
    hins_of_slabClear hs1 hpos hlo hhi hE0 hE1⟩

/-! ## Ball geometry for a `Real.sqrt` radius (the emitted bands use `R = √q`, `q` rational) -/







end EdgeClearGlue


/-  BandGlue.lean -- brick K0 of the ANDURIL Arb discharge
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 1.3: `segBandHyp_of_bands`).

    THE GAP IT CLOSES.  The h280000 capstone
    `AllZeros_h280000_Indexed.all_nontrivial_zeros_up_to_height_280000` takes
    `hbands : ∀ k, k < 280 → SegBandHyp k`, and each `SegBandHyp k` is a list of BOX CLAIMS
    ("every zero of ζ in `[1/4000000, 3999999/4000000] x [segLo k i, segHi k i]` is on the line").
    Every box claim is the conclusion of one emitted band theorem `RHInBoxT_*.rh_in_box_*`, but the
    capstone ASSUMES the claims: nothing composes them.  This file makes the composition a theorem,
    parametric in the per-band Arb inputs, so a future evaluator only has to supply those inputs.

    CONTENTS.
      * `BandData`: the parameters of one Turing band, i.e. the arguments of the canonical
        `TuringBand.BandStatement` other than the strip.  `Stmt`, `LineHyp`, `ArbHyp`, `EnclHyp`,
        `Box`, `Inputs`.  `stmt_iff` checks, by `Iff.rfl`, that `LineHyp`/`ArbHyp` are EXACTLY the
        two binders of `BandStatement` (so `Inputs` is what `hLine`/`hArbT` ask for, verbatim).
      * `stmt_of_valid`: the band statement from its decidable side conditions (pins, ball
        geometry), via `TuringBand.turing_band_on_line`; the generic proof of every `rh_in_box_*`.
      * K0 generic: `segBandHyp_of_bands` (indexed band table: the `SegBandHyp` shape),
        `segBandHyp_of_bandList` (a `List` of bands), `ladder_of_bands` (a ladder of segments: the
        `∀ k, k < K → SegBandHyp k` shape the capstone consumes).  Bands may COVER their boxes
        (`T0 ≤ lo`, `hi ≤ T1`); the emitted ladder has equality.
      * K0 + K1: `ReducedInputs` (on-line zeros, two one-sided edge-clearance slabs, five
        enclosures) and `CapGeom` (decidable ball-cap geometry); `inputs_of_reduced`,
        `segBandHyp_of_reduced`, `ladder_of_reduced` (per-band slab heights).  With K1 the `hnzl`
        binder disappears and `hnzb`/`hnzt`/`hins` reduce to two zero-free slabs per band.
      * Certificate form: `BoxCert σ0 σ1 lo hi` (some band covering the box, with its statement
        and its inputs), constructors `of_stmt` / `of_valid` / `of_reduced`, and
        `segBandHyp_of_certs`, `ladder_of_certs`.  A future evaluator may pick its own band
        parameters here (for instance enclosures much wider than the 1e-12 Arb ones, as long as
        the pins hold), which the fixed-table form does not allow.

    The real-segment instantiation (segment 0 of the ladder, 25 bands, the real `rh_in_box_*`
    theorems) is `BandGlue_h1000.lean`.

    Trust: every theorem here is proved outright from its stated hypotheses; axioms
    [propext, Classical.choice, Quot.sound] (see AxiomGuardBandGlue.lean).  No `sorry`.

    conjecture1_proved = False.  Glue for a finite verification up to a fixed height; nothing
    here says anything about the Riemann Hypothesis. -/





open Complex

namespace BandGlue





namespace BandData

variable (σ0 σ1 : ℝ) (d : BandData)















variable {σ0 σ1 d}







/-! ## K1 inside the band: the reduced per-band input -/







/-- **K1 applied to a band**: the reduced input and the cap geometry give the full `Inputs`. -/
theorem inputs_of_reduced {δ0 δ1 : ℝ} (hG : d.CapGeom δ0 δ1) (h : d.ReducedInputs δ0 δ1) :
    d.Inputs := by
  obtain ⟨hL, hE0, hE1, hEn⟩ := h
  obtain ⟨hnzb, hnzt, hnzl, hins⟩ :=
    EdgeClearGlue.hArbT_nonvanishing_of_edge_clear d.hs1 hG.hT0 hG.hT1 hG.hδ0 hG.hδ1
      hG.hpos hG.hlo hG.hhi hE0 hE1
  exact ⟨hL, hnzb, hnzt, hnzl, hins, hEn⟩



end BandData

open BandData

/-! ## Band certificates for a box -/





/-- A certificate from a band theorem (for instance an emitted `rh_in_box_*`) and its inputs. -/
theorem BoxCert.of_stmt {σ0 σ1 lo hi : ℝ} (d : BandData) (hlo : d.T0 ≤ lo) (hhi : hi ≤ d.T1)
    (hS : d.Stmt σ0 σ1) (hin : d.Inputs) : BoxCert σ0 σ1 lo hi :=
  ⟨d, hlo, hhi, hS, hin⟩





/-! ## K0: segments and ladders -/















end BandGlue


/-  ArgChangeGlue.lean -- bricks K6a + K6b + K6c consumed by the K0/K1 band glue
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 1.3; `BandGlue.lean`,
    `EdgeClearGlue.lean`).

    `BandGlue.BandData.EnclHyp` is the five-enclosure tail of the `hArbT` binder of every emitted
    Turing band.  After this file:
      * conjunct 5 (`hAV2`, σ = 2 vertical of ζ) is discharged for EVERY band by K6a
        (`ArgZetaTwo.hAV2_of_le`), given the rational side condition `[L1, H1] ⊇ [-249/250, 249/250]`;
      * conjuncts 8, 9 (`hAG1`, `hAG2`, Γℝ verticals) are discharged for every band with
        `0 ≤ T0`, `0 ≤ T1` by K6b (`ArgGammaR.hAG1_of_bounds`, `hAG2_of_bounds`), given rational
        side conditions comparing `L4 H4 L5 H5` with the closed-form brackets `Sm1`, `S2`;
      * conjuncts 6, 7 (`hAHt`, `hAHb`, the horizontal edges) remain as `HorizHyp`, which K6c
        (`ArgHoriz.hAH_of_octCert_boxes`) reduces to an octant certificate plus two point
        enclosures per edge (`HorizHyp.of_octCerts`).
    Combined with K1 (`EdgeClearGlue`), the per-band input becomes `K6Inputs`: the on-line zeros,
    two zero-free edge slabs and the two horizontal enclosures.  `BoxCert.of_K6`,
    `segBandHyp_of_K6` and `ladder_of_K6` feed it into the K0 composition unchanged.

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  Glue for a finite verification up to a fixed height. -/






open Complex

namespace ArgChangeGlue

open BandGlue BandGlue.BandData





/-- **K6a + K6b inside a band**: the five enclosures from the side conditions and the two
    horizontal ones. -/
theorem enclHyp_of_K6 {d : BandData} (hS : K6Side d) (hH : HorizHyp d) : d.EnclHyp :=
  ⟨ArgZetaTwo.hAV2_of_le hS.hL1 hS.hH1, hH.1, hH.2,
    ArgGammaR.hAG1_of_bounds hS.hT0 hS.hT1 hS.hL4 hS.hH4,
    ArgGammaR.hAG2_of_bounds hS.hT0 hS.hT1 hS.hL5 hS.hH5⟩















/-! ## Band-table helpers (for emitted K6 segments) -/



/-- `CapGeom` only depends on `T0`, `T1`, `c`, `R`: it transfers between band data that agree on
    them (for instance a band and its K6 re-parametrisation). -/
theorem capGeom_transfer {δ0 δ1 : ℝ} {d d' : BandData} (hT0 : d'.T0 = d.T0) (hT1 : d'.T1 = d.T1)
    (hc : d'.c = d.c) (hR : d'.R = d.R) (h : d.CapGeom δ0 δ1) : d'.CapGeom δ0 δ1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨by rw [hT0]; exact h1, by rw [hT1]; exact h2, h3, h4, by rw [hc, hR]; exact h5,
    by rw [hT0, hc, hR]; exact h6, by rw [hT1, hc, hR]; exact h7⟩

/-! ## K6a feeding K6c: the `x = 2` endpoint of every horizontal edge -/





end ArgChangeGlue


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







open Arb4 Arb4.Q






theorem solution {lo hi δ0 δ1 : ℝ} (d : BandData) (E : EnclQ) (hlo : d.T0 ≤ lo)
    (hhi : hi ≤ d.T1) (hV : ValidS (1 / 4000000) (3999999 / 4000000) (withEncl d E))
    (hG : d.CapGeom δ0 δ1) (hL : d.LineHyp) (hs0 : EdgeClearGlue.SlabClear (d.T0 - δ0) d.T0)
    (hs1 : EdgeClearGlue.SlabClear d.T1 (d.T1 + δ1)) (hS : ArgChangeGlue.K6Side (withEncl d E))
    (hH1 : DiffractionCore.argChangeHoriz riemannZeta d.T1 2 (-1) ∈ Set.Icc E.L2.val E.H2.val)
    (hH0 : DiffractionCore.argChangeHoriz riemannZeta d.T0 2 (-1) ∈ Set.Icc E.L3.val E.H3.val) :
    BoxCert (1 / 4000000) (3999999 / 4000000) lo hi :=
  BoxCert.of_stmt (withEncl d E) hlo hhi (stmt_of_validS hV)
    (inputs_of_reduced (ArgChangeGlue.capGeom_transfer (d := d) (d' := withEncl d E) rfl rfl rfl rfl hG)
      ⟨hL, hs0, hs1, ArgChangeGlue.enclHyp_of_K6 hS ⟨hH1, hH0⟩⟩)

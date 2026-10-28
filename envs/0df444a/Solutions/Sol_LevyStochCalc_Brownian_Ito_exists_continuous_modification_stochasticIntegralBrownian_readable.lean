-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.exists_continuous_modification_stochasticIntegralBrownian_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:29:28.429324+00:00
-- url     : https://prove2.me/submissions/ca5b940b-ac89-40f4-ac9a-74af6154a90a

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_kolmogorovChentsov_modification_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_stochasticIntegralBrownian_sub_pow_four_le_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
theorem LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg : 0 ≤ gaussianFourthMoment :=
  integral_nonneg fun x => by positivity
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoQuadVarSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section ContinuousModification
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
/-- The extended distance between two reals is the norm of their difference. -/
theorem LevyStochCalc.Brownian.Ito.edist_eq_coe_nnnorm_sub (x y : ℝ) : edist x y = (‖x - y‖₊ : ℝ≥0∞) := by
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
  exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
include hℱ hC0 hCH in
/-- **A continuous modification of the `L²` Itô integral of a bounded integrand.** The
fourth-moment increment bound is the Kolmogorov–Chentsov condition with exponents `(4, 2)`. -/
theorem solution :
    ∃ Y : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂P, Continuous fun t => Y t ω)
        ∧ ∀ t : ℝ, 0 ≤ t →
            Y t =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
  classical
  set K : ℝ := (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 with hK
  have hK0 : 0 ≤ K := by
    have := LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg
    positivity
  set Xc : ℝ → Ω → ℝ :=
    fun t ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (max t 0) ω with hXc
  have hXmeas : ∀ t : ℝ, Measurable (Xc t) := fun t =>
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq (max t 0)).mono
      (ℱ.le _)).measurable
  -- the Kolmogorov condition with exponents `(4, 2)`
  have hpair : ∀ a b : ℝ, 0 ≤ a → a < b →
      ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
        ≤ ENNReal.ofReal (K * (b - a) ^ 2) := by
    intro a b ha hab
    have hswap : ∀ ω : Ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω‖₊ : ℝ≥0∞)
        = (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) := by
      intro ω
      rw [← nnnorm_neg, neg_sub]
    simp_rw [hswap]
    exact LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_pow_four_le_readable W ℱ hℱ H hm hp hq hC0 hCH ha hab
  have hkol : ∀ s t : ℝ, ∫⁻ ω, edist (Xc s ω) (Xc t ω) ^ (4 : ℝ) ∂P
      ≤ (K.toNNReal : ℝ≥0∞) * edist s t ^ (2 : ℝ) := by
    intro s t
    have hnat4 : ∀ ω : Ω, edist (Xc s ω) (Xc t ω) ^ (4 : ℝ)
        = (‖Xc s ω - Xc t ω‖₊ : ℝ≥0∞) ^ (4 : ℕ) := by
      intro ω
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast,
        LevyStochCalc.Brownian.Ito.edist_eq_coe_nnnorm_sub]
    have hnat2 : edist s t ^ (2 : ℝ) = ENNReal.ofReal (|s - t| ^ 2) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, edist_dist,
        Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _)]
    have hdiff : |max s 0 - max t 0| ≤ |s - t| := abs_max_sub_max_le_abs s t 0
    simp_rw [hnat4]
    rw [hnat2, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      Real.coe_toNNReal K hK0]
    rcases lt_trichotomy (max s 0) (max t 0) with hst | hst | hst
    · refine le_trans (hpair (max s 0) (max t 0) (le_max_right _ _) hst) ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : max t 0 - max s 0 ≤ |s - t| := by
        rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ max t 0 - max s 0), abs_sub_comm]
        exact hdiff
      have h2 : (0 : ℝ) ≤ max t 0 - max s 0 := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 2) hK0
    · have hzero : ∀ ω : Ω, (‖Xc s ω - Xc t ω‖₊ : ℝ≥0∞) ^ (4 : ℕ) = 0 := by
        intro ω
        simp [hXc, hst]
      simp_rw [hzero]
      simp
    · have hswap : ∀ ω : Ω, (‖Xc s ω - Xc t ω‖₊ : ℝ≥0∞)
          = (‖Xc t ω - Xc s ω‖₊ : ℝ≥0∞) := fun ω => by rw [← nnnorm_neg, neg_sub]
      simp_rw [hswap]
      refine le_trans (hpair (max t 0) (max s 0) (le_max_right _ _) hst) ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : max s 0 - max t 0 ≤ |s - t| := by
        rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ max s 0 - max t 0)]
        exact hdiff
      have h2 : (0 : ℝ) ≤ max s 0 - max t 0 := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 2) hK0
  have hKolProc : ProbabilityTheory.IsKolmogorovProcess Xc P 4 2 K.toNNReal :=
    ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology hXmeas hkol
      (by norm_num) (by norm_num)
  obtain ⟨Y, hYcont, hYmod⟩ :=
    LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification_readable P Xc hKolProc
      (by norm_num)
  refine ⟨Y, hYcont, fun t ht => ?_⟩
  have h := hYmod t
  simp only [hXc, max_eq_left ht] at h
  exact h

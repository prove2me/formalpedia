-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_energy_sub_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:21:29.689761+00:00
-- url     : https://prove2.me/submissions/f00daf8d-1a2c-497c-a0a5-1d2ecc72589a

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionSup

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLinear.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
/-- The squared extended norm of a real number is the extended real of its square. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq (z : ℝ) : (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) := by
  rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from (ofReal_norm z).symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
section Energy
variable {H₁ H₂ : Ω → ℝ → ℝ}
/-- The energy density of an integrand is measurable in the sample point. -/
theorem LevyStochCalc.Brownian.Ito.measurable_energyDensity (hm : Measurable (Function.uncurry H₁)) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
  have hf : Measurable fun p : Ω × ℝ => (‖H₁ p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    (((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2)
  exact hf.lintegral_prod_right'
/-- The squared extended norm of a difference is dominated by twice the sum of the squares. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul (x y : ℝ) :
    (‖x - y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x + y)])
end Energy
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionSup.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u
section SupBound
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
omit [IsProbabilityMeasure P] in
/-- The energy of a difference is controlled by the energies of the two differences with a common
third integrand. -/
theorem solution {f g h : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hh : Measurable (Function.uncurry h)) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s - g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
  have hptw : ∀ (ω : Ω) (s : ℝ), (‖f ω s - g ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 + (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s
    have hb := LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul (f ω s - h ω s) (g ω s - h ω s)
    simpa [sub_sub_sub_cancel_right] using hb
  have hmfh : Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := LevyStochCalc.Brownian.Ito.measurable_energyDensity (hf.sub hh) T
  have hmgh : Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := LevyStochCalc.Brownian.Ito.measurable_energyDensity (hg.sub hh) T
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s - g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          2 * ((‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2
            + (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
        MeasureTheory.lintegral_mono fun ω => MeasureTheory.lintegral_mono fun s => hptw ω s
    _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
        have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            2 * ((‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2
              + (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume
            = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) := by
          intro ω
          have hfhm : Measurable fun s : ℝ => (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 := by
            have h1 : Measurable fun s : ℝ => f ω s - h ω s :=
              (Measurable.of_uncurry_left hf).sub (Measurable.of_uncurry_left hh)
            exact ((h1.nnnorm).coe_nnreal_ennreal).pow_const 2
          rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
            MeasureTheory.lintegral_add_left hfhm]
        simp only [hinner]
        rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
          MeasureTheory.lintegral_add_left hmfh]

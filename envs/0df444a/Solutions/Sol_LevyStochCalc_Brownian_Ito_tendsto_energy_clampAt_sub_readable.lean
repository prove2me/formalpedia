-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.tendsto_energy_clampAt_sub_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:20:35.539367+00:00
-- url     : https://prove2.me/submissions/00303c34-ada7-44c7-90e4-3b42927d20d4

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoTruncate

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
section Energy
variable {H₁ H₂ : Ω → ℝ → ℝ}
/-- The energy density of an integrand is measurable in the sample point. -/
theorem LevyStochCalc.Brownian.Ito.measurable_energyDensity (hm : Measurable (Function.uncurry H₁)) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
  have hf : Measurable fun p : Ω × ℝ => (‖H₁ p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    (((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2)
  exact hf.lintegral_prod_right'
end Energy
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoTruncate.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal Topology
section Clamp
theorem LevyStochCalc.abs_clampAt_sub_le {j : ℝ} (hj : 0 ≤ j) (x : ℝ) : |clampAt j x - x| ≤ |x| := by
  unfold clampAt
  rcases le_or_gt x (-j) with hx | hx
  · rw [min_eq_right (by linarith : x ≤ j), max_eq_left hx,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ -j - x), abs_of_nonpos (by linarith : x ≤ 0)]
    linarith
  · rcases le_or_gt x j with hx' | hx'
    · rw [min_eq_right hx', max_eq_right hx.le]
      simp
    · rw [min_eq_left hx'.le, max_eq_right (by linarith : -j ≤ j),
        abs_of_nonpos (by linarith : j - x ≤ 0), abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
      linarith
theorem LevyStochCalc.clampAt_eq_self {j x : ℝ} (hx : |x| ≤ j) : clampAt j x = x := by
  rw [abs_le] at hx
  unfold clampAt
  rw [min_eq_right hx.2, max_eq_right hx.1]
end Clamp
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
theorem LevyStochCalc.Brownian.Ito.eventually_clampAt_eq (x : ℝ) : ∀ᶠ j : ℕ in Filter.atTop, clampAt (j : ℝ) x = x := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  filter_upwards [Filter.eventually_ge_atTop N] with j hj
  exact clampAt_eq_self (hN.le.trans (by exact_mod_cast hj))
/-- **Clamping an integrand converges to it in energy on every window.** -/
theorem solution {G : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry G))
    {T : ℝ} (hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (fun j : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) := by
  have hmc : ∀ j : ℕ, Measurable (Function.uncurry fun ω s => LevyStochCalc.clampAt (j : ℝ) (G ω s)) :=
    fun j => (LevyStochCalc.continuous_clampAt (j : ℝ)).measurable.comp hm
  have hbmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := LevyStochCalc.Brownian.Ito.measurable_energyDensity hm T
  have hFmeas : ∀ j : ℕ, Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun j => LevyStochCalc.Brownian.Ito.measurable_energyDensity ((hmc j).sub hm) T
  have hptw : ∀ (j : ℕ) (ω : Ω) (s : ℝ),
      (‖LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖G ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro j ω s
    have habs : |LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s| ≤ |G ω s| :=
      LevyStochCalc.abs_clampAt_sub_le (Nat.cast_nonneg j) _
    have hle : (‖LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ≤ (‖G ω s‖₊ : ℝ≥0∞) := by
      refine ENNReal.coe_le_coe.mpr ?_
      rw [← NNReal.coe_le_coe]
      simpa [Real.norm_eq_abs] using habs
    gcongr
  have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun j : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) Filter.atTop (𝓝 0) := by
    filter_upwards [MeasureTheory.ae_lt_top hbmeas hq] with ω hfin
    have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (F := fun (j : ℕ) (s : ℝ) => (‖LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2)
      (f := fun _s : ℝ => (0 : ℝ≥0∞))
      (bound := fun s => (‖G ω s‖₊ : ℝ≥0∞) ^ 2)
      (fun j => ((((LevyStochCalc.continuous_clampAt ((j : ℕ) : ℝ)).measurable.comp
          (Measurable.of_uncurry_left hm)).sub
        (Measurable.of_uncurry_left hm)).nnnorm.coe_nnreal_ennreal).pow_const 2)
      (fun j => Filter.Eventually.of_forall fun s => hptw j ω s) hfin.ne ?_
    · simpa using hlim
    · filter_upwards with s
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (LevyStochCalc.Brownian.Ito.eventually_clampAt_eq (G ω s))
      refine tendsto_atTop_of_eventually_const (i₀ := N) fun j hj => ?_
      rw [hN j hj]
      simp
  have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (μ := P)
    (F := fun (j : ℕ) (ω : Ω) => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    (f := fun _ω : Ω => (0 : ℝ≥0∞))
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    hFmeas
    (fun j => Filter.Eventually.of_forall fun ω =>
      MeasureTheory.lintegral_mono fun s => hptw j ω s) hq hinner
  simpa using hlim

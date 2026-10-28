-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.ae_eq_of_solvesOn_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:26:02.033469+00:00
-- url     : https://prove2.me/submissions/5b0a48b5-5107-4e52-ab2c-6961c1f95caf

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow
import Theorems.Thm_LevyStochCalc_Ito_Picard_ae_eq_zero_of_bieleckiNorm_eq_zero_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_bieleckiNorm_lt_top_of_supL2_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_bieleckiNorm_sub_lt_top_of_lt_top_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_exists_bieleckiWeight_rate_lt_one_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardWindow.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
omit [MeasurableSpace E] in
/-- Two path maps agreeing a.s. at every time of the window have equal Bielecki norms. -/
theorem LevyStochCalc.Ito.Picard.bieleckiNorm_congr_ae_on (β T : ℝ) {Y Z : ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, Y t =ᵐ[P] Z t) :
    bieleckiNorm (P := P) β T Y = bieleckiNorm (P := P) β T Z := by
  unfold bieleckiNorm
  refine iSup_congr fun t => iSup_congr fun ht => ?_
  have hinner : (∫⁻ ω, ∑ i, (‖Y t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [h t ht] with ω hω
    rw [hω]
  rw [hinner]
/-- A finite extended real dominated by a strict multiple of itself vanishes. -/
theorem LevyStochCalc.Ito.Picard.eq_zero_of_le_mul_self {a q : ℝ≥0∞} (ha : a ≠ ⊤) (hq : q < 1) (h : a ≤ q * a) :
    a = 0 := by
  by_contra h0
  have hlt : a * q < a * 1 := ENNReal.mul_lt_mul_right h0 ha hq
  rw [mul_one] at hlt
  rw [mul_comm q a] at h
  exact absurd h (not_le.mpr hlt)
section Solves
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (x₀ : Fin n → ℝ)
/-- **Uniqueness on a window.** Two solutions of the equation on `[0, T]` relative to the same
filtration, each with a finite `S²` norm, agree almost surely at every time of the window. -/
theorem solution
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {X Y : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X)) (hYm : Measurable (Function.uncurry Y))
    (hXS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hX : LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T)
    (hY : LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n, X t ω i = Y t ω i := by
  obtain ⟨hσmX, hσpX, hσsX, hγmX, hγpX, hγsX, heqX⟩ := hX
  obtain ⟨hσmY, hσpY, hσsY, hγmY, hγpY, hγsY, heqY⟩ := hY
  obtain ⟨β, hβ, hq⟩ := LevyStochCalc.Ito.Picard.exists_bieleckiWeight_rate_lt_one_readable (n := n) (d := d) (T := T) L hT
  set q := (ENNReal.ofReal
      ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
        / (2 * β))) ^ ((1 : ℝ) / 2) with hqdef
  have hXe := LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_lt_top_of_supL2 hXS
  have hYe := LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_lt_top_of_supL2 hYS
  have hswapX : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω) :=
    hXm.comp (measurable_snd.prodMk measurable_fst)
  have hswapY : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Y s ω) :=
    hYm.comp (measurable_snd.prodMk measurable_fst)
  have hsubm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω - Y s ω) :=
    hswapX.sub hswapY
  have hnorm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖) :=
    hsubm.norm
  have hcontr := LevyStochCalc.Ito.Picard.bieleckiNorm_picardStep_diff_le W N ℱ hℱW hℱN coeffs hLip X Y x₀
    hσmX hσpX hσsX hγmX hγpX hγsX hσmY hσpY hσsY hγmY hγpY hγsY
    (fun i => LevyStochCalc.Ito.Picard.measurable_mu_comp_state coeffs hReg hXm i)
    (fun i => LevyStochCalc.Ito.Picard.measurable_mu_comp_state coeffs hReg hYm i)
    hnorm
    (fun i b _ => LevyStochCalc.Ito.Picard.lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip hXe i (by assumption))
    (fun i b _ => LevyStochCalc.Ito.Picard.lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip hYe i (by assumption))
    (fun b _ => LevyStochCalc.Ito.Picard.lintegral_sq_sub_lt_top_of_energy hXm hYm hXe hYe b)
    hsubm hβ hT
  have hcongr : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i)
      = LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i =>
          LevyStochCalc.Ito.Picard.picardStep W N ℱ hℱW hℱN coeffs X x₀ hσmX hσpX hσsX hγmX hγpX hγsX t ω i
            - LevyStochCalc.Ito.Picard.picardStep W N ℱ hℱW hℱN coeffs Y x₀ hσmY hσpY hσsY hγmY hγpY hγsY t ω i) := by
    refine LevyStochCalc.Ito.Picard.bieleckiNorm_congr_ae_on β T fun t ht => ?_
    filter_upwards [heqX t ht, heqY t ht] with ω hωX hωY
    funext i
    rw [hωX i, hωY i]
  have hfin : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) ≠ ⊤ :=
    (LevyStochCalc.Ito.Picard.bieleckiNorm_sub_lt_top_of_lt_top_readable hβ.le T hXm hYm
      (LevyStochCalc.Ito.Picard.bieleckiNorm_lt_top_of_supL2_readable hT hXS) (LevyStochCalc.Ito.Picard.bieleckiNorm_lt_top_of_supL2_readable hT hYS)).ne
  have hle : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i)
      ≤ q * LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) := by
    rw [hqdef]
    conv_lhs => rw [hcongr]
    exact hcontr
  have hzero : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) = 0 :=
    LevyStochCalc.Ito.Picard.eq_zero_of_le_mul_self hfin hq hle
  intro t ht
  have hsl : ∀ (u : ℝ) (i : Fin n), Measurable fun ω => X u ω i - Y u ω i := by
    intro u i
    exact ((measurable_pi_apply i).comp (Measurable.of_uncurry_left hXm)).sub
      ((measurable_pi_apply i).comp (Measurable.of_uncurry_left hYm))
  filter_upwards [LevyStochCalc.Ito.Picard.ae_eq_zero_of_bieleckiNorm_eq_zero_readable hsl hzero ht] with ω hω
  intro i
  exact sub_eq_zero.mp (hω i)

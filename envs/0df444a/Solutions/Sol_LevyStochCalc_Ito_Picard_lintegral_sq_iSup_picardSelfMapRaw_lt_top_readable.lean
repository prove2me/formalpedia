-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardSelfMapRaw_lt_top_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:34:33.658452+00:00
-- url     : https://prove2.me/submissions/7da91fe2-e8ee-406e-88e3-0d5a5e3d80e6

import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardSupL2
import Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_iSup_picardStep_lt_top_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_measurable_picardStepOnRawStop_slice_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_picardSelfMapRaw_ae_eq_readable
import Theorems.Thm_LevyStochCalc_Probability_enorm_dyadicRunMax_readable
import Theorems.Thm_LevyStochCalc_Probability_iSup_enorm_eq_iSup_dyadicRunMax_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {M : ℝ → Ω → ℝ} {T : ℝ}
/-- Each sampled running maximum is measurable when the sampled slices are. -/
theorem LevyStochCalc.Probability.measurable_enorm_dyadicRunMax (hM : ∀ t : ℝ, Measurable (M t)) (T : ℝ) (n : ℕ) :
    Measurable fun ω => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  have heq : (fun ω => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞))
      = fun ω => ⨆ k : Fin (2 ^ n + 1), (‖M (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) :=
    funext fun ω => enorm_dyadicRunMax_readable M T n ω
  rw [heq]
  exact Measurable.iSup fun k =>
    ENNReal.continuous_coe.measurable.comp (hM (dyadicTime T n (k : ℕ))).nnnorm
/-- The supremum over the window of a sum of squared coordinates is bounded by the sum of the
squared coordinatewise suprema. -/
theorem LevyStochCalc.Probability.iSup_sum_sq_le {n' : ℕ} (A : ℝ → Ω → (Fin n' → ℝ)) (T : ℝ) (ω : Ω) :
    (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖A (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2)
      ≤ ∑ i, (⨆ t : Set.Icc (0 : ℝ) T, (‖A (t : ℝ) ω i‖₊ : ℝ≥0∞)) ^ 2 := by
  refine iSup_le fun t => Finset.sum_le_sum fun i _ => ?_
  exact pow_le_pow_left' (le_iSup (fun u : Set.Icc (0 : ℝ) T =>
    (‖A (u : ℝ) ω i‖₊ : ℝ≥0∞)) t) 2
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardSupL2.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
/-- **The Picard self-map along a raw state process has finite `S²` norm on every window.** -/
theorem solution
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Z < ⊤) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i,
        (‖(LevyStochCalc.Ito.Picard.picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb).X
          (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
  set Y := LevyStochCalc.Ito.Picard.picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb with hY
  set St := LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ with hSt
  have hZsm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z (min s T) ω) :=
    hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have hZe := LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le
  -- the step at the frozen process has finite `S²` norm
  have hstep : ∀ i : Fin n, ∫⁻ ω,
      (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω => St t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := fun i =>
    LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardStep_lt_top_readable W N ℱ hℱW hℱN coeffs
      (fun s ω => Z (min s T) ω) x₀
      (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg hZm T)
      (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
      (fun i' j _ hb => LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
        (Z := fun s ω => Z (min s T) ω) hZsm hZe i' j hb)
      (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg hZm T)
      (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
      (fun i' _ hb => LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
        (Z := fun s ω => Z (min s T) ω) hZsm hZe i' hb)
      (LevyStochCalc.Ito.Picard.measurable_mu_rawStop coeffs hReg hZm T)
      (fun i' b hb => LevyStochCalc.Ito.Picard.lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
        (Z := fun s ω => Z (min s T) ω) hZe i' hb)
      i hT'
  -- the modification agrees at all dyadic points simultaneously
  have hae : ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ, Y.X (LevyStochCalc.Probability.dyadicTime T' p.1 p.2) ω
      = St (LevyStochCalc.Probability.dyadicTime T' p.1 p.2) ω := by
    rw [MeasureTheory.ae_all_iff]
    exact fun p => LevyStochCalc.Ito.Picard.picardSelfMapRaw_ae_eq_readable W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
      hZm hZa hZb (LevyStochCalc.Probability.dyadicTime T' p.1 p.2)
  have hcad : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ),
      Filter.Tendsto (fun s => Y.X s ω i) (nhdsWithin t (Set.Ioi t)) (nhds (Y.X t ω i)) := by
    filter_upwards [Y.cadlag_paths] with ω hω i t
    exact ((continuous_apply i).tendsto _).comp (hω t).1
  have hStm : ∀ i : Fin n, ∀ t : ℝ, Measurable fun ω => St t ω i := fun i t =>
    LevyStochCalc.Ito.Picard.measurable_picardStepOnRawStop_slice_readable W N ℱ hℱW hℱN coeffs hReg hLip x₀
      hZm hZa hZb hT.le t i
  calc ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y.X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ ∫⁻ ω, ∑ i, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω => St t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae, hcad] with ω hω hc
        refine le_trans (LevyStochCalc.Probability.iSup_sum_sq_le (fun t ω => Y.X t ω) T' ω) (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LevyStochCalc.Probability.iSup_enorm_eq_iSup_dyadicRunMax_readable hT'.le (hc i)]
        congr 1
        refine iSup_congr fun m => ?_
        rw [LevyStochCalc.Probability.enorm_dyadicRunMax_readable, LevyStochCalc.Probability.enorm_dyadicRunMax_readable]
        exact iSup_congr fun k => by rw [congrFun (hω (m, (k : ℕ))) i]
    _ = ∑ i, ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω => St t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P :=
        lintegral_finsetSum _ fun i _ =>
          (Measurable.iSup fun m => LevyStochCalc.Probability.measurable_enorm_dyadicRunMax (hStm i) T' m).pow_const 2
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun i _ => hstep i

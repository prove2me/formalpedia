-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.lintegral_sq_iSup_diffusion_lt_top_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:28:16.551986+00:00
-- url     : https://prove2.me/submissions/0e1e4ae9-a38c-4ab3-baf6-d27a698245c9

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionApi
import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardSupL2
import Theorems.Thm_LevyStochCalc_Probability_enorm_dyadicRunMax_readable
import Theorems.Thm_LevyStochCalc_Probability_lintegral_sq_dyadicRunMax_le_readable
import Theorems.Thm_LevyStochCalc_Probability_sq_sum_le_card_sq_mul_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionApi.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Itô L² isometry.**

  `𝔼[ (∫_0^T H_s dW_s)² ] = 𝔼[ ∫_0^T |H_s|² ds ]`

for predictable square-integrable `H`. ENNReal form.

Forwards to the L²-isometry conjunct of `itoIsometry_brownian_unified_existence`. -/
theorem LevyStochCalc.Brownian.Ito.itoIsometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (T : ℝ) (hT : 0 < T)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq_int_global T ω‖₊
      : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ((‖H ω s‖₊ : ℝ≥0∞))^2 ∂volume ∂P := by
  unfold stochasticIntegral
  exact isometry_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global hT
end
end

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
/-- Refining the level does not move the partition points: level `n`'s point `k` is level
`n + 1`'s point `2 * k`. -/
theorem LevyStochCalc.Probability.dyadicTime_succ_two_mul {T : ℝ} (n k : ℕ) :
    dyadicTime T (n + 1) (2 * k) = dyadicTime T n k := by
  unfold dyadicTime
  congr 1
  push_cast
  rw [pow_succ]
  ring
variable {M : ℝ → Ω → ℝ} {T : ℝ}
/-- Refining the level can only increase the sampled running maximum. -/
theorem LevyStochCalc.Probability.enorm_dyadicRunMax_mono (M : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    Monotone fun n => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [enorm_dyadicRunMax_readable, enorm_dyadicRunMax_readable]
  refine iSup_le fun k => ?_
  refine le_iSup_of_le ⟨2 * (k : ℕ), ?_⟩ (le_of_eq ?_)
  · have hk : (k : ℕ) ≤ 2 ^ n := Nat.lt_succ_iff.mp k.isLt
    calc 2 * (k : ℕ) ≤ 2 * 2 ^ n := by omega
      _ < 2 ^ (n + 1) + 1 := by rw [pow_succ]; omega
  · rw [dyadicTime_succ_two_mul]
/-- Each sampled running maximum is measurable when the sampled slices are. -/
theorem LevyStochCalc.Probability.measurable_enorm_dyadicRunMax (hM : ∀ t : ℝ, Measurable (M t)) (T : ℝ) (n : ℕ) :
    Measurable fun ω => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  have heq : (fun ω => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞))
      = fun ω => ⨆ k : Fin (2 ^ n + 1), (‖M (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) :=
    funext fun ω => enorm_dyadicRunMax_readable M T n ω
  rw [heq]
  exact Measurable.iSup fun k =>
    ENNReal.continuous_coe.measurable.comp (hM (dyadicTime T n (k : ℕ))).nnnorm
/-- Squaring commutes with the supremum of a monotone sequence. -/
theorem LevyStochCalc.Probability.iSup_sq_of_monotone {a : ℕ → ℝ≥0∞} (ha : Monotone a) :
    (⨆ n, a n) ^ 2 = ⨆ n, a n ^ 2 := by
  refine le_antisymm ?_ (iSup_le fun n => pow_le_pow_left' (le_iSup a n) 2)
  rw [pow_two, ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => le_iSup_of_le (max n m) ?_
  rw [pow_two]
  exact mul_le_mul' (ha (le_max_left n m)) (ha (le_max_right n m))
/-- **Doob's `L²` inequality over the dyadic points.** No path regularity is needed: the
supremum runs over the countable family of partition points. -/
theorem LevyStochCalc.Probability.lintegral_iSup_dyadicRunMax_sq_le {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} (hM : MeasureTheory.Martingale M ℱ μ) (hT : 0 ≤ T) :
    ∫⁻ ω, (⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)) ^ 2 ∂μ
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have hMm : ∀ t : ℝ, Measurable (M t) := fun t => ((hM.1 t).mono (ℱ.le t)).measurable
  have heq : (fun ω => (⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)) ^ 2)
      = fun ω => ⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 :=
    funext fun ω => iSup_sq_of_monotone (enorm_dyadicRunMax_mono M T ω)
  rw [heq, lintegral_iSup (fun n => (measurable_enorm_dyadicRunMax hMm T n).pow_const 2)
    (fun m n hmn ω => pow_le_pow_left' (enorm_dyadicRunMax_mono M T ω hmn) 2)]
  exact iSup_le fun n => lintegral_sq_dyadicRunMax_le_readable hM hT n
/-- The sampled running maximum of a finite sum is bounded by the sum of the running maxima. -/
theorem LevyStochCalc.Probability.enorm_dyadicRunMax_sum_le {ι : Type*} (s : Finset ι) (A : ι → ℝ → Ω → ℝ) (T : ℝ)
    (n : ℕ) (ω : Ω) :
    (‖dyadicRunMax (fun t ω => ∑ j ∈ s, A j t ω) T n ω‖₊ : ℝ≥0∞)
      ≤ ∑ j ∈ s, (‖dyadicRunMax (A j) T n ω‖₊ : ℝ≥0∞) := by
  rw [enorm_dyadicRunMax_readable]
  refine iSup_le fun k => ?_
  have hpt : (‖∑ j ∈ s, A j (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞)
      ≤ ∑ j ∈ s, (‖A j (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) := by
    rw [← ENNReal.ofNNReal_finsetSum]
    exact ENNReal.coe_le_coe.mpr (nnnorm_sum_le _ _)
  refine le_trans hpt (Finset.sum_le_sum fun j _ => ?_)
  rw [enorm_dyadicRunMax_readable]
  exact le_iSup (fun m : Fin (2 ^ n + 1) =>
    (‖A j (dyadicTime T n (m : ℕ)) ω‖₊ : ℝ≥0∞)) k
/-- The supremum of the sampled running maxima of a finite sum is bounded by the sum of the
suprema. -/
theorem LevyStochCalc.Probability.iSup_dyadicRunMax_sum_le {ι : Type*} (s : Finset ι) (A : ι → ℝ → Ω → ℝ) (T : ℝ)
    (ω : Ω) :
    (⨆ n, (‖dyadicRunMax (fun t ω => ∑ j ∈ s, A j t ω) T n ω‖₊ : ℝ≥0∞))
      ≤ ∑ j ∈ s, ⨆ n, (‖dyadicRunMax (A j) T n ω‖₊ : ℝ≥0∞) :=
  iSup_le fun n => le_trans (enorm_dyadicRunMax_sum_le s A T n ω)
    (Finset.sum_le_sum fun j _ => le_iSup (fun m => (‖dyadicRunMax (A j) T m ω‖₊ : ℝ≥0∞)) n)
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
omit [MeasurableSpace E] in
/-- Doob's inequality for one Brownian coordinate of the Picard step. -/
theorem LevyStochCalc.Ito.Picard.lintegral_sq_iSup_brownian_coord_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) (j : Fin d) {T' : ℝ} (hT' : 0 ≤ T') :
    ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω =>
        LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j)
          (h_meas i j) (h_progMeas i j) (h_sq i j) t ω) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 4 * ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j)
          (h_meas i j) (h_progMeas i j) (h_sq i j) T' ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  obtain ⟨F, hF⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral (W.W j) ℱ (hℱW j)
    (fun ω' s => coeffs.σ s (X s ω') i j) (h_meas i j) (h_progMeas i j) (h_sq i j)
  exact lintegral_iSup_dyadicRunMax_sq_le hF hT'
omit [MeasurableSpace E] in
/-- Slice measurability of one Brownian coordinate's integral. -/
theorem LevyStochCalc.Ito.Picard.measurable_brownianIntegral_slice
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) (j : Fin d) (t : ℝ) :
    Measurable fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j) (h_meas i j) (h_progMeas i j) (h_sq i j) t ω := by
  obtain ⟨F, hF⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral (W.W j) ℱ (hℱW j)
    (fun ω' s => coeffs.σ s (X s ω') i j) (h_meas i j) (h_progMeas i j) (h_sq i j)
  exact (hF.stronglyMeasurable t).measurable.mono (F.le t) le_rfl
omit [MeasurableSpace E] in
/-- The dyadic supremum of the Brownian component, summed over the driving coordinates. -/
theorem solution
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω =>
        LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i)
        T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
  set g : Fin d → ℝ → Ω → ℝ := fun j t ω =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j) t ω with hg
  have hunfold : (fun t (ω : Ω) =>
      LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i)
      = fun t ω => ∑ j : Fin d, g j t ω := rfl
  have hmeas : ∀ j : Fin d, ∀ t : ℝ, Measurable (g j t) := fun j t =>
    LevyStochCalc.Ito.Picard.measurable_brownianIntegral_slice W ℱ hℱW coeffs X h_meas h_progMeas h_sq i j t
  have hsupm : ∀ j : Fin d, Measurable fun ω =>
      (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (g j) T' m ω‖₊ : ℝ≥0∞)) ^ 2 :=
    fun j => (Measurable.iSup fun m => LevyStochCalc.Probability.measurable_enorm_dyadicRunMax (hmeas j) T' m).pow_const 2
  calc ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω => ∑ j : Fin d, g j t ω) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ ∫⁻ ω, ((Finset.univ.card : ℝ≥0∞) ^ 2
          * ∑ j : Fin d, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (g j) T' m ω‖₊ : ℝ≥0∞)) ^ 2) ∂P :=
        lintegral_mono fun ω => le_trans
          (pow_le_pow_left' (LevyStochCalc.Probability.iSup_dyadicRunMax_sum_le Finset.univ g T' ω) 2)
          (LevyStochCalc.Probability.sq_sum_le_card_sq_mul_readable Finset.univ _)
    _ = (Finset.univ.card : ℝ≥0∞) ^ 2
          * ∑ j : Fin d, ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (g j) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum _ fun j _ => hsupm j]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (by simp) (ENNReal.sum_lt_top.mpr fun j _ => ?_)
        refine lt_of_le_of_lt (LevyStochCalc.Ito.Picard.lintegral_sq_iSup_brownian_coord_le W ℱ hℱW coeffs X
          h_meas h_progMeas h_sq i j hT'.le) ?_
        refine ENNReal.mul_lt_top (by norm_num) ?_
        refine lt_of_le_of_lt ?_ (h_sq i j T' hT')
        exact le_of_eq (LevyStochCalc.Brownian.Ito.itoIsometry (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j) T' hT'
          (h_meas i j) (h_progMeas i j) (h_sq i j))

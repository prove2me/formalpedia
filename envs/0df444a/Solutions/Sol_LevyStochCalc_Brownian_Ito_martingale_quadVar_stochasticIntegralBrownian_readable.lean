-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.martingale_quadVar_stochasticIntegralBrownian_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:23:56.122228+00:00
-- url     : https://prove2.me/submissions/8a88197f-1092-4d13-9f32-ce676b3ee6f7

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_simpleIntegral_sq_sub_compensator_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_masterApprox_compensator_tendsto_L1_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_setIntegral_eval_sq_Icc_clamped_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_eLpNorm_one_sq_sub_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section MasterSequence
variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include h_meas h_sq_int_global in
/-- The `H`-compensator `A_t = ∫₀ᵗ H² ds` is `P`-integrable (`t ≥ 0`). -/
lemma LevyStochCalc.Brownian.Ito.compensatorH_integrable {t : ℝ} (ht : 0 ≤ t) :
    MeasureTheory.Integrable (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · exact (compensatorH_memLp_prod H h_meas h_sq_int_global ht').integrable_sq.integral_prod_left
  · have heq : (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) = fun _ => (0 : ℝ) := by
      funext ω; rw [← ht', Set.Icc_self, MeasureTheory.setIntegral_measure_zero _ (by simp)]
    rw [heq]; exact MeasureTheory.integrable_const 0
include h_progMeas in
/-- The `H`-compensator `A_t = ∫₀ᵗ H² ds` is `ℱ_t`-adapted. -/
lemma LevyStochCalc.Brownian.Ito.compensatorH_adapted (t : ℝ) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) := by
  rcases le_or_gt 0 t with ht | ht
  · have hsq : Probability.ProgressivelyMeasurable ℱ fun ω s => (H ω s) ^ 2 :=
      (continuous_pow 2).comp_progressivelyMeasurable (by simp) h_progMeas
    exact hsq.stronglyMeasurable_setIntegral measurableSet_Icc Set.Icc_subset_Iic_self volume
  · have heq : (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) = fun _ => (0 : ℝ) := by
      funext ω; rw [Set.Icc_eq_empty (not_le.mpr ht)]; simp
    rw [heq]; exact stronglyMeasurable_const
include h_meas h_progMeas h_sq_int_global hℱ in
/-- **Conjunct 2: the compensated square is a martingale.**
`t ↦ (F t)² − ∫₀ᵗ H² ds` is an `ℱ`-martingale. The simple-level
compensated squares `martingale_simpleIntegral_sq_sub_compensator` (for `masterApprox n`)
are martingales converging in `L¹` to the `F`-process: the integrand-squares converge
(`masterApprox_tendsto_L2` + `tendsto_eLpNorm_one_sq_sub`) and the compensators
converge (`masterApprox_compensator_tendsto_L1`). -/
lemma solution :
    MeasureTheory.Martingale
      (fun t ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume)
      ℱ P := by
  set F := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global with hF
  have hAHint : ∀ t, MeasureTheory.Integrable
      (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact LevyStochCalc.Brownian.Ito.compensatorH_integrable H h_meas h_sq_int_global ht
    · have heq : (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) = fun _ => (0 : ℝ) := by
        funext ω; rw [Set.Icc_eq_empty (not_le.mpr ht)]; simp
      rw [heq]; exact MeasureTheory.integrable_const 0
  refine LevyStochCalc.Brownian.Ito.martingale_of_tendsto_eLpNorm_one
    (M := fun n t ω =>
      (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t,
            ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
    (fun n => LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_sq_sub_compensator_readable W ℱ hℱ (LevyStochCalc.Brownian.Ito.master_horizon_pos n)
      (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n))
    (fun n t => (LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_sq_sub_compensator_readable W ℱ hℱ (LevyStochCalc.Brownian.Ito.master_horizon_pos n)
      (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n)).integrable t)
    (fun t => ?_) (fun t => ?_) (fun t => ?_)
  · -- StronglyAdapted
    have hFsq : @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ t) (fun ω => (F t ω) ^ 2) := by
      simpa [pow_two, Pi.mul_def] using
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas
          h_sq_int_global t).mul
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas h_sq_int_global t)
    exact hFsq.sub (LevyStochCalc.Brownian.Ito.compensatorH_adapted ℱ H h_progMeas t)
  · -- integrability of the F-process at each `t`
    exact ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global t).integrable_sq).sub
      (hAHint t)
  · -- `L¹`-convergence of the simple compensated squares to the F-process
    rcases le_or_gt 0 t with ht | ht
    · have hX : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
          (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
            h_sq_int_global n) t ω) ^ 2
            - (F t ω) ^ 2) 1 P) Filter.atTop (nhds 0) :=
        LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub_readable
          (fun n => (Finset.measurable_sum _ (fun i _ =>
            ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).mul
              ((W.measurable_eval _).sub (W.measurable_eval _)))).aemeasurable)
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
            h_sq_int_global t).1.aemeasurable
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).2.ne
          (LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2 W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht)
      have hY := LevyStochCalc.Brownian.Ito.masterApprox_compensator_tendsto_L1_readable ℱ H h_meas h_progMeas h_sq_int_global ht
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using hX.add hY)
        (Filter.Eventually.of_forall (fun n => bot_le))
        (Filter.Eventually.of_forall (fun n => ?_))
      have hXaesm : MeasureTheory.AEStronglyMeasurable
          (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
            h_sq_int_global n) t ω) ^ 2
            - (F t ω) ^ 2) P :=
        (((Finset.measurable_sum _ (fun i _ =>
          ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).mul
            ((W.measurable_eval _).sub (W.measurable_eval _)))).pow_const
              2).aestronglyMeasurable).sub
          ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
            h_sq_int_global t).1.aemeasurable.pow_const 2).aestronglyMeasurable
      have hAn_meas : Measurable (fun ω => ∫ u in Set.Icc (0 : ℝ) t,
          ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume) := by
        rw [show (fun ω => ∫ u in Set.Icc (0 : ℝ) t,
              ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
            = fun ω => ∑ i : Fin (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).N,
                (min ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).partition i.succ) t
                  - min ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).partition
                      i.castSucc) t)
                  * ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ i ω) ^ 2 from
          funext (fun ω => LevyStochCalc.Brownian.Ito.setIntegral_eval_sq_Icc_clamped_readable
            (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) ω)]
        exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
          (((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).pow_const 2))
      have hYaesm : MeasureTheory.AEStronglyMeasurable
          (fun ω => (∫ u in Set.Icc (0 : ℝ) t,
              ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P :=
        hAn_meas.aestronglyMeasurable.sub (hAHint t).aestronglyMeasurable
      calc MeasureTheory.eLpNorm
            ((fun t' ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
              h_sq_int_global n) t' ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t', ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
                  h_sq_int_global n).eval u ω) ^ 2 ∂volume) t
              - fun ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P
          = MeasureTheory.eLpNorm
              ((fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
                h_sq_int_global n) t ω) ^ 2
                  - (F t ω) ^ 2)
                - fun ω => (∫ u in Set.Icc (0 : ℝ) t,
                    ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
                  - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P := by
            refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
            simp only [Pi.sub_apply]; ring
        _ ≤ _ := MeasureTheory.eLpNorm_sub_le hXaesm hYaesm le_rfl
    · have hzero : ∀ n, MeasureTheory.eLpNorm
          ((fun t' ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
            h_sq_int_global n) t' ω) ^ 2
              - ∫ u in Set.Icc (0 : ℝ) t', ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
                h_sq_int_global n).eval u ω) ^ 2 ∂volume) t
            - fun ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P = 0 := by
        intro n
        refine (MeasureTheory.eLpNorm_eq_zero_of_ae_zero ?_)
        filter_upwards [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas
          h_sq_int_global ht] with ω hF0
        simp only [Pi.sub_apply, Pi.zero_apply,
          LevyStochCalc.Brownian.Ito.simpleIntegral_eq_zero_of_nonpos W _ (le_of_lt ht) ω, hF, hF0,
          Set.Icc_eq_empty (not_le.mpr ht)]
        simp
      simp only [hzero]; exact tendsto_const_nhds

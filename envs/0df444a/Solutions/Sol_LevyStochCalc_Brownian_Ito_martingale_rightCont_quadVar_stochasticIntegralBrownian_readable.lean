-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.martingale_rightCont_quadVar_stochasticIntegralBrownian_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:25:52.128525+00:00
-- url     : https://prove2.me/submissions/82883a54-f657-47ef-bf89-c329503bdf2f

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionApi
import Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_quadVar_stochasticIntegralBrownian_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_eLpNorm_one_sq_sub_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
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
end MasterSequence
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionApi.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
include h_meas h_progMeas h_sq_int_global hℱ in
/-- **Conjunct 2 on `rightCont`: `(F)² − ∫₀ᵗH²` is a `rightCont`-martingale.**
The `ℱ`-martingale (`martingale_quadVar_stochasticIntegralBrownian`) lifts
via right-`L¹`-continuity: the `F²`-part is controlled by `F`'s right-`L²`-continuity
(`tendsto_eLpNorm_one_sq_sub`), the compensator part by the horizon slab
`∫⁻∫⁻_{(s,r]}‖H‖² → 0` (`tendsto_setLIntegral_Ioc_prod_zero`). -/
lemma solution :
    MeasureTheory.Martingale
      (fun t ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume)
      ℱ.rightCont P := by
  refine LevyStochCalc.Martingale.martingale_rightCont_of_tendsto_eLpNorm_one
    (LevyStochCalc.Brownian.Ito.martingale_quadVar_stochasticIntegralBrownian_readable W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
    (fun s => ?_)
  set F := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global with hFdef
  -- `F²`-part: right-`L¹`-continuity of the square.
  have hF2 : Filter.Tendsto (fun r => MeasureTheory.eLpNorm
      (fun ω => (F r ω) ^ 2 - (F s ω) ^ 2) 1 P) (nhdsWithin s (Set.Ioi s)) (nhds 0) :=
    LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub_readable (l := nhdsWithin s (Set.Ioi s)) (a := fun r => F r) (b := F s)
      (fun r => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global r).1.aemeasurable)
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global s).1.aemeasurable
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global s).2.ne
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eLpNorm_two_right_tendsto W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global s)
  -- compensator part: right-`L¹`-continuity of `A_t = ∫₀ᵗ H²`.
  have hA : Filter.Tendsto (fun r => MeasureTheory.eLpNorm
      (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
    rcases le_or_gt 0 s with hs | hs
    · have hslab := LevyStochCalc.Brownian.Ito.tendsto_setLIntegral_Ioc_prod_zero (fun ω u => (‖H ω u‖₊ : ℝ≥0∞) ^ 2)
        ((h_meas.nnnorm.coe_nnreal_ennreal).pow_const 2) hs (lt_add_one s)
        (h_sq_int_global (s + 1) (by linarith)).ne
      refine hslab.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hsr : s ≤ r := le_of_lt hr
      have hrpos : 0 < r := lt_of_le_of_lt hs hr
      have hHr : ∀ᵐ ω ∂P, MeasureTheory.Integrable
          (fun u => (H ω u) ^ 2) (volume.restrict (Set.Icc (0 : ℝ) r)) :=
        (LevyStochCalc.Brownian.Ito.compensatorH_memLp_prod H h_meas h_sq_int_global hrpos).integrable_sq.prod_right_ae
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      refine (lintegral_congr_ae ?_).symm
      filter_upwards [hHr] with ω hHrω
      have hHsω : MeasureTheory.Integrable (fun u => (H ω u) ^ 2)
          (volume.restrict (Set.Icc (0 : ℝ) s)) :=
        hHrω.mono_measure (MeasureTheory.Measure.restrict_mono (Set.Icc_subset_Icc_right hsr)
          (le_refl _))
      have hHscω : MeasureTheory.Integrable (fun u => (H ω u) ^ 2)
          (volume.restrict (Set.Ioc s r)) :=
        hHrω.mono_measure (MeasureTheory.Measure.restrict_mono
          (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_left hs)) (le_refl _))
      have hsplit : (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume
          = ∫ u in Set.Ioc s r, (H ω u) ^ 2 ∂volume := by
        rw [← Set.Icc_union_Ioc_eq_Icc hs hsr,
          MeasureTheory.setIntegral_union
            (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)))
            measurableSet_Ioc hHsω hHscω]
        ring
      rw [hsplit, ← ofReal_norm, Real.norm_eq_abs,
        abs_of_nonneg (MeasureTheory.integral_nonneg (fun u => sq_nonneg _)),
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hHscω
          (Filter.Eventually.of_forall (fun u => sq_nonneg _))]
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
      rw [show (‖H ω u‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((H ω u) ^ 2) from by
        rw [show (‖H ω u‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖H ω u‖ from (ofReal_norm _).symm,
          ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]]
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Ioo_mem_nhdsGT hs] with r hr
      have hAr : (fun u => (H · u) ^ 2) = (fun u => (H · u) ^ 2) := rfl
      symm
      rw [show (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) = (0 : Ω → ℝ) from by
        funext ω
        rw [Set.Icc_eq_empty (not_le.mpr hr.2), Set.Icc_eq_empty (not_le.mpr hs)]
        simp]
      exact MeasureTheory.eLpNorm_zero
  -- combine the two parts.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hF2.add hA)
    (Filter.Eventually.of_forall (fun r => bot_le)) (Filter.Eventually.of_forall (fun r => ?_))
  have hF2aesm : MeasureTheory.AEStronglyMeasurable (fun ω => (F r ω) ^ 2 - (F s ω) ^ 2) P :=
    (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global r).1.aemeasurable.pow_const
        2).aestronglyMeasurable).sub
      (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global s).1.aemeasurable.pow_const
        2).aestronglyMeasurable)
  have hAaesm : MeasureTheory.AEStronglyMeasurable
      (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) P :=
    ((LevyStochCalc.Brownian.Ito.compensatorH_adapted ℱ H h_progMeas r).mono
      (ℱ.le r)).aestronglyMeasurable.sub
      (((LevyStochCalc.Brownian.Ito.compensatorH_adapted ℱ H h_progMeas s).mono
        (ℱ.le s)).aestronglyMeasurable)
  calc MeasureTheory.eLpNorm
        ((fun t ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) r
          - fun ω => (F s ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P
      = MeasureTheory.eLpNorm
          ((fun ω => (F r ω) ^ 2 - (F s ω) ^ 2)
            - fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
              - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P := by
        refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
        simp only [Pi.sub_apply]; ring
    _ ≤ _ := MeasureTheory.eLpNorm_sub_le hF2aesm hAaesm le_rfl

-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:27:26.041531+00:00
-- url     : https://prove2.me/submissions/8cd58217-66c0-48f9-9c50-b8066eaa70cd

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum
import Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_rightCont_quadVar_stochasticIntegralBrownian_readable

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
end MasterSequence
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
section QuadVarIncrement
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include hℱ in
/-- The compensated square increment is conditionally centred at its left endpoint. -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    P[LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b | ℱ.rightCont a] =ᵐ[P] 0 := by
  have hMmart := LevyStochCalc.Brownian.Ito.martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H hm hp hq
  have hQmart := LevyStochCalc.Brownian.Ito.martingale_rightCont_quadVar_stochasticIntegralBrownian_readable W ℱ hℱ H hm hp hq
  have hMmem : ∀ t : ℝ, MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t) 2 P :=
    fun t => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H hm hp hq t
  have hMint : ∀ t : ℝ, Integrable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t) P :=
    fun t => (hMmem t).integrable (by norm_num)
  have hAint : ∀ t : ℝ, 0 ≤ t →
      Integrable (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P :=
    fun t ht => LevyStochCalc.Brownian.Ito.compensatorH_integrable H hm hq ht
  have hMsq : ∀ t : ℝ,
      Integrable (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω) ^ 2) P := by
    intro t
    have hfun : (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω) ^ 2)
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t
          * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact (hMmem t).integrable_mul (hMmem t)
  have hb : (0 : ℝ) ≤ b := ha.trans hab
  -- the three pieces of the decomposition
  have hi1 : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) ^ 2
      - ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume) P := (hMsq b).sub (hAint b hb)
  have hi2 : Integrable (fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
      * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) P :=
    (hMmem a).integrable_mul (hMmem b)
  have hi3 : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
      + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) P := (hMsq a).add (hAint a ha)
  have hdecomp : LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b
      = (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        + ((-2 : ℝ) • fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
            * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω)
        + (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
            + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) := by
    funext ω
    simp only [LevyStochCalc.Brownian.Ito.quadVarIncrement, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- conditional expectations of the three pieces
  have h1 : P[fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume | ℱ.rightCont a]
      =ᵐ[P] fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume := hQmart.2 a b hab
  have h2 : P[fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω | ℱ.rightCont a]
      =ᵐ[P] fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2 := by
    have hMa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont a)
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a) := hMmart.1 a
    have hkey := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := ℱ.rightCont a)
      hMa hi2 (hMint b)
    have hfun : (fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω)
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a
          * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b := rfl
    rw [hfun]
    filter_upwards [hkey, hMmart.2 a b hab] with ω hω hω'
    rw [hω, Pi.mul_apply, hω', pow_two]
  have h3 : P[fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume | ℱ.rightCont a]
      =ᵐ[P] fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume := by
    refine Filter.EventuallyEq.of_eq (MeasureTheory.condExp_of_stronglyMeasurable
      (ℱ.rightCont.le a) ?_ hi3)
    have hMa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont a)
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a) := hMmart.1 a
    have hAa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont a)
        (fun ω => ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) :=
      (LevyStochCalc.Brownian.Ito.compensatorH_adapted ℱ H hp a).mono (ℱ.le_rightCont a)
    exact ((hMa.measurable.pow_const 2).stronglyMeasurable).add hAa
  -- assemble
  rw [hdecomp]
  have hadd1 := MeasureTheory.condExp_add hi1 (hi2.smul (-2 : ℝ)) (ℱ.rightCont a)
  have hadd2 := MeasureTheory.condExp_add (hi1.add (hi2.smul (-2 : ℝ))) hi3 (ℱ.rightCont a)
  have hsmul := MeasureTheory.condExp_smul (μ := P) (m := ℱ.rightCont a) (-2 : ℝ)
    (fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
      * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω)
  filter_upwards [hadd2, hadd1, hsmul, h1, h2, h3] with ω e2 e1 es f1 f2 f3
  rw [e2, Pi.add_apply, e1, Pi.add_apply, es, Pi.smul_apply, f1, f2, f3, Pi.zero_apply]
  simp only [smul_eq_mul]
  ring

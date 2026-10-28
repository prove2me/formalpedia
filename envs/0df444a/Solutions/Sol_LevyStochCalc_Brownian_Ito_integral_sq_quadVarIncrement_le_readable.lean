-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:31:58.506079+00:00
-- url     : https://prove2.me/submissions/39830961-49bc-4211-bccf-bc9fdabb9781

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum
import Theorems.Thm_LevyStochCalc_Brownian_Ito_compensator_sub_bounds_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_stochasticIntegralBrownian_sub_pow_four_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_memLp_two_sq_increment_readable

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
end MasterSequence
end
end

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
section IncrementL2
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
include hm hq hC0 hCH in
/-- The compensator increment lies in `L²`. -/
theorem LevyStochCalc.Brownian.Ito.memLp_two_compensator_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MemLp (fun ω => (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
      - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) 2 P := by
  have hint := ((compensatorH_integrable H hm hq (ha.trans hab)).sub
    (compensatorH_integrable H hm hq ha))
  refine MeasureTheory.MemLp.of_bound hint.aestronglyMeasurable (C ^ 2 * (b - a)) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  obtain ⟨h1, h2⟩ := compensator_sub_bounds_readable H hm hC0 hCH ha hab ω
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  exact h2
include hℱ hC0 hCH in
/-- The compensated square increment lies in `L²`. -/
theorem LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (quadVarIncrement W ℱ hℱ H hm hp hq a b) 2 P :=
  (memLp_two_sq_increment_readable W ℱ hℱ H hm hp hq hC0 hCH ha hab).sub
    (memLp_two_compensator_sub H hm hq hC0 hCH ha hab.le)
include hℱ hC0 hCH in
/-- Second moment of the compensated square increment. -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2 ∂P
      ≤ (2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * C ^ 4 * (b - a) ^ 2 := by
  have hcg : (0 : ℝ) ≤ LevyStochCalc.Brownian.Ito.gaussianFourthMoment := LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hXmem := LevyStochCalc.Brownian.Ito.memLp_two_sq_increment_readable W ℱ hℱ H hm hp hq hC0 hCH ha hab
  have hYmem := LevyStochCalc.Brownian.Ito.memLp_two_compensator_sub H hm hq hC0 hCH ha hab.le
  have hXint : Integrable (fun ω => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2) P := by
    have hfun : (fun ω => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
        = (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2)
          * (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact hXmem.integrable_mul hXmem
  have hYint : Integrable (fun ω => ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
      - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2) P := by
    have hfun : (fun ω => ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2)
        = (fun ω => (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume)
          * (fun ω => (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact hYmem.integrable_mul hYmem
  -- the fourth moment of the increment
  have hX : ∫ ω, ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2 ∂P
      ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by
    have hK : (0 : ℝ) ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by positivity
    have heq : ENNReal.ofReal (∫ ω, ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2) ∂P :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hXint
        (Filter.Eventually.of_forall fun ω => by positivity)
    have hpt : ∀ ω : Ω, ENNReal.ofReal (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
        = (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 := by
      have key : ∀ x : ℝ, ENNReal.ofReal ((x ^ 2) ^ 2) = (‖x‖₊ : ℝ≥0∞) ^ 4 := by
        intro x
        have h1 : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal |x| := by
          rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
          exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
        rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
        congr 1
        ring
      exact fun ω => key _
    rw [← ENNReal.ofReal_le_ofReal_iff hK, heq]
    simp_rw [hpt]
    exact LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_pow_four_le_readable W ℱ hℱ H hm hp hq hC0 hCH ha hab
  -- the compensator increment
  have hY : ∫ ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ∂P
      ≤ C ^ 4 * (b - a) ^ 2 := by
    have hbnd : ∀ ω : Ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ≤ C ^ 4 * (b - a) ^ 2 := by
      intro ω
      obtain ⟨h1, h2⟩ := LevyStochCalc.Brownian.Ito.compensator_sub_bounds_readable H hm hC0 hCH ha hab.le ω
      nlinarith [sq_nonneg C, mul_nonneg (mul_nonneg hC0 hC0) hba]
    calc ∫ ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ∂P
        ≤ ∫ _ω : Ω, C ^ 4 * (b - a) ^ 2 ∂P :=
          MeasureTheory.integral_mono hYint (integrable_const _) hbnd
      _ = C ^ 4 * (b - a) ^ 2 := by simp
  -- combine
  have hptwise : ∀ ω : Ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2
      ≤ 2 * (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
        + 2 * (((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2) := by
    intro ω
    simp only [LevyStochCalc.Brownian.Ito.quadVarIncrement]
    nlinarith [sq_nonneg ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
      + ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume))]
  have hζint : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2) P := by
    have hmem := LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H hm hp hq hC0 hCH ha hab
    have hfun : (fun ω => (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2)
        = LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact hmem.integrable_mul hmem
  calc ∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2 ∂P
      ≤ ∫ ω, (2 * (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
          + 2 * (((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2)) ∂P :=
        MeasureTheory.integral_mono hζint ((hXint.const_mul 2).add (hYint.const_mul 2)) hptwise
    _ = 2 * (∫ ω, ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2 ∂P)
          + 2 * (∫ ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ∂P) := by
        rw [MeasureTheory.integral_add (hXint.const_mul 2) (hYint.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) + 2 * (C ^ 4 * (b - a) ^ 2) := by
        gcongr
    _ = (2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * C ^ 4 * (b - a) ^ 2 := by ring

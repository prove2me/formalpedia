-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.condExp_polarQuadVarIncrement_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:31:14.623308+00:00
-- url     : https://prove2.me/submissions/6e356751-d7bd-41bd-94c9-4ae34a38644c

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_PolarisedQuadVar
import Theorems.Thm_LevyStochCalc_Brownian_Ito_compensator_add_sq_eq_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_compensator_sub_bounds_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_condExp_quadVarIncrement_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_memLp_two_sq_increment_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_add_readable

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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoQuadVarSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
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
end IncrementL2
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/PolarisedQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Polarised
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H₁ H₂ : Ω → ℝ → ℝ)
  (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
  (hp₁ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₁)
  (hp₂ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₂)
  (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
  (hpa : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
  (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include hℱ in
/-- Additivity of the Itô integral in the integrand, at every nonnegative time. -/
theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_add_ae_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t ω
        + stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t ω := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · filter_upwards [stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ
        (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa (le_refl (0 : ℝ)),
      stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H₁ hm₁ hp₁ hq₁ (le_refl (0 : ℝ)),
      stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H₂ hm₂ hp₂ hq₂ (le_refl (0 : ℝ))]
      with ω e0 e1 e2
    rw [e0, e1, e2, Pi.zero_apply, add_zero]
  · exact stochasticIntegralBrownian_add_readable W ℱ hℱ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ hma hpa hqa ht'
section Bounds
variable {C : ℝ} (hC0 : 0 ≤ C) (hCH₁ : ∀ ω s, |H₁ ω s| ≤ C) (hCH₂ : ∀ ω s, |H₂ ω s| ≤ C)
include hℱ hC0 hCH₁ hCH₂ in
/-- **Polarisation.** Twice the compensated product is the compensated square increment of
`H₁ + H₂` less those of `H₁` and of `H₂`. -/
theorem LevyStochCalc.Brownian.Ito.smul_two_polarQuadVarIncrement_ae {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (2 : ℝ) • polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b
      =ᵐ[P] fun ω =>
        quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
          - quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
          - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω := by
  have hb : (0 : ℝ) ≤ b := ha.trans hab
  filter_upwards [stochasticIntegralBrownian_add_ae_of_nonneg W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂
      hq₁ hq₂ hma hpa hqa hb,
    stochasticIntegralBrownian_add_ae_of_nonneg W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
      hma hpa hqa ha] with ω eb ea
  simp only [Pi.smul_apply, smul_eq_mul, polarQuadVarIncrement, quadVarIncrement]
  rw [eb, ea, compensator_add_sq_eq_readable H₁ H₂ hm₁ hm₂ hC0 hCH₁ hCH₂ ω,
    compensator_add_sq_eq_readable H₁ H₂ hm₁ hm₂ hC0 hCH₁ hCH₂ ω]
  ring
include hℱ hma hpa hqa hC0 hCH₁ hCH₂ in
/-- **The compensated product is conditionally centred at the left endpoint.** -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b | ℱ.rightCont a]
      =ᵐ[P] 0 := by
  have hC20 : (0 : ℝ) ≤ 2 * C := by linarith
  have hb₁ : ∀ ω s, |H₁ ω s| ≤ 2 * C := fun ω s => (hCH₁ ω s).trans (by linarith)
  have hb₂ : ∀ ω s, |H₂ ω s| ≤ 2 * C := fun ω s => (hCH₂ ω s).trans (by linarith)
  have hba : ∀ ω s, |H₁ ω s + H₂ ω s| ≤ 2 * C := fun ω s =>
    (abs_add_le _ _).trans (by linarith [hCH₁ ω s, hCH₂ ω s])
  have iAdd := (LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab).integrable (by norm_num)
  have i₁ := (LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab).integrable
    (by norm_num)
  have i₂ := (LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab).integrable
    (by norm_num)
  have cAdd := LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement_readable W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa ha hab.le
  have c₁ := LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement_readable W ℱ hℱ H₁ hm₁ hp₁ hq₁ ha hab.le
  have c₂ := LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement_readable W ℱ hℱ H₂ hm₂ hp₂ hq₂ ha hab.le
  have e1 := MeasureTheory.condExp_sub (iAdd.sub i₁) i₂ (ℱ.rightCont a)
  have e2 := MeasureTheory.condExp_sub iAdd i₁ (ℱ.rightCont a)
  have hcond0 : P[LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b
        - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b
        - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b | ℱ.rightCont a] =ᵐ[P] 0 := by
    filter_upwards [e1, e2, cAdd, c₁, c₂] with ω h1 h2 hA hh1 hh2
    rw [h1, Pi.sub_apply, h2, Pi.sub_apply, hA, hh1, hh2, Pi.zero_apply]
    ring
  have hpol := LevyStochCalc.Brownian.Ito.smul_two_polarQuadVarIncrement_ae W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab.le
  have hkey := (MeasureTheory.condExp_congr_ae hpol).trans hcond0
  have hsm := MeasureTheory.condExp_smul (μ := P) (m := ℱ.rightCont a) (2 : ℝ)
    (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b)
  filter_upwards [hkey, hsm] with ω h1 h2
  rw [h2, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  rw [Pi.zero_apply]
  linarith

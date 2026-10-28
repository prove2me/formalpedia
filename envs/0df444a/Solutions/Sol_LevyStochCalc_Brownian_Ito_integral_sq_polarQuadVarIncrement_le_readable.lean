-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_sq_polarQuadVarIncrement_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:33:46.934078+00:00
-- url     : https://prove2.me/submissions/5f897149-121a-4c0c-ba53-8fa931d06b49

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_PolarisedQuadVar
import Theorems.Thm_LevyStochCalc_Brownian_Ito_compensator_add_sq_eq_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_compensator_sub_bounds_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sq_quadVarIncrement_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_memLp_two_polarQuadVarIncrement_readable
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
/-- **Second moment of the compensated product.** -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Integrable (fun ω =>
        (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2) P
      ∧ ∫ ω, (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2 ∂P
        ≤ 3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4) * (b - a) ^ 2 := by
  have hC20 : (0 : ℝ) ≤ 2 * C := by linarith
  have hb₁ : ∀ ω s, |H₁ ω s| ≤ 2 * C := fun ω s => (hCH₁ ω s).trans (by linarith)
  have hb₂ : ∀ ω s, |H₂ ω s| ≤ 2 * C := fun ω s => (hCH₂ ω s).trans (by linarith)
  have hba : ∀ ω s, |H₁ ω s + H₂ ω s| ≤ 2 * C := fun ω s =>
    (abs_add_le _ _).trans (by linarith [hCH₁ ω s, hCH₂ ω s])
  have mAdd := LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab
  have m₁ := LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab
  have m₂ := LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab
  have lAdd := LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le_readable W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab
  have l₁ := LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le_readable W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab
  have l₂ := LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le_readable W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab
  have hmp := LevyStochCalc.Brownian.Ito.memLp_two_polarQuadVarIncrement_readable W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab
  have iA : Integrable (fun ω =>
      (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2) P :=
    mAdd.integrable_sq
  have i₁ : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2) P :=
    m₁.integrable_sq
  have i₂ : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2) P :=
    m₂.integrable_sq
  have iS₁ : Integrable (fun ω =>
      (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2) P := iA.add i₁
  have iS : Integrable (fun ω =>
      (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2) P := iS₁.add i₂
  have hdom : Integrable (fun ω => 3 / 4 *
      ((LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2)) P := iS.const_mul _
  have hpol := LevyStochCalc.Brownian.Ito.smul_two_polarQuadVarIncrement_ae W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab.le
  have hpt : (fun ω =>
      (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2)
      ≤ᵐ[P] fun ω => 3 / 4 *
        ((LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
          + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2
          + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2) := by
    filter_upwards [hpol] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul] at hω
    have hpe : LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω
        = (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
            - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
            - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) / 2 := by linarith
    rw [hpe]
    nlinarith [sq_nonneg (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
        + LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω),
      sq_nonneg (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
        + LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω),
      sq_nonneg (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
        - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω)]
  have hsplit : ∫ ω,
      ((LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2) ∂P
      = (∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2 ∂P)
        + (∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2 ∂P)
        + ∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2 ∂P := by
    rw [MeasureTheory.integral_add iS₁ i₂, MeasureTheory.integral_add iA i₁]
  refine ⟨hmp.integrable_sq, ?_⟩
  have hstep : ∫ ω,
      (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2 ∂P
      ≤ 3 / 4 * ((∫ ω,
          (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2 ∂P)
        + (∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2 ∂P)
        + ∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2 ∂P) := by
    have := MeasureTheory.integral_mono_ae hmp.integrable_sq hdom hpt
    rwa [MeasureTheory.integral_const_mul, hsplit] at this
  refine hstep.trans ?_
  have hC4 : (0 : ℝ) ≤ (2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4 := by
    have hcg : (0 : ℝ) ≤ LevyStochCalc.Brownian.Ito.gaussianFourthMoment := LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg
    positivity
  have hba2 : (0 : ℝ) ≤ (b - a) ^ 2 := sq_nonneg _
  nlinarith [lAdd, l₁, l₂, mul_nonneg hC4 hba2]

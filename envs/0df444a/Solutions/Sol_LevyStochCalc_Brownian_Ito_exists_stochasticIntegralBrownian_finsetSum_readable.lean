-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:14:40.658851+00:00
-- url     : https://prove2.me/submissions/aed9a044-bc0a-432a-a6a9-2b7553bca2db

import Definitions.Def_KLSModular_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoZero
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFinsetSum
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_energy_lt_top_of_bound_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_add_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_ae_zero_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/Progressive.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
section
variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω}
section Add
variable [NormedAddCommGroup E] {ℱ : MeasureTheory.Filtration ℝ mΩ}
/-- The pointwise sum of two progressively measurable processes is progressively measurable. -/
theorem LevyStochCalc.Probability.ProgressivelyMeasurable.add {A B : Ω → ℝ → E} (hA : ProgressivelyMeasurable ℱ A)
    (hB : ProgressivelyMeasurable ℱ B) :
    ProgressivelyMeasurable ℱ fun ω s => A ω s + B ω s := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => A p.1 s + B p.1 s) p.2)
      = fun p : Ω × ℝ =>
        (Set.Iic t).indicator (A p.1) p.2 + (Set.Iic t).indicator (B p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, add_zero]
  rw [key]
  exact (hA t).add (hB t)
end Add
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The `L²` Itô integral depends on the integrand only through the function itself. -/
theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {F₁ F₂ : Ω → ℝ → ℝ} (hEq : F₁ = F₂)
    (hm₁ : Measurable (Function.uncurry F₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ F₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry F₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ F₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (t : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ F₁ hm₁ hp₁ hq₁ t
      = stochasticIntegralBrownian W ℱ hℱ F₂ hm₂ hp₂ hq₂ t := by
  subst hEq; rfl
end
end

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
/-- The squared extended norm of a real number is the extended real of its square. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq (z : ℝ) : (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) := by
  rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from (ofReal_norm z).symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
section Energy
variable {H₁ H₂ : Ω → ℝ → ℝ}
/-- The squared extended norm of a sum is dominated by twice the sum of the squares. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul (x y : ℝ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - y)])
end Energy
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoZero.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
/-- A constant process is progressively measurable for any filtration. -/
theorem LevyStochCalc.Probability.progressivelyMeasurable_const {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [TopologicalSpace E] [Zero E] (ℱ : Filtration ℝ mΩ) (c : E) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => c) := fun _ =>
  stronglyMeasurable_const.indicator
    (measurableSet_preimage measurable_snd measurableSet_Iic)
/-- The zero process is progressively measurable for any filtration. -/
theorem LevyStochCalc.Probability.progressivelyMeasurable_zero {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [TopologicalSpace E] [Zero E] (ℱ : Filtration ℝ mΩ) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => (0 : E)) :=
  Probability.progressivelyMeasurable_const ℱ 0
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFinsetSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
/-- The square-integrability of an integrand transfers along an equality of integrands. -/
theorem LevyStochCalc.Brownian.Ito.energy_lt_top_congr {F₁ F₂ : Ω → ℝ → ℝ} (h : F₁ = F₂)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  subst h
  exact hq
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ in
/-- **The Itô integral of a finite sum of integrands is the sum of their integrals.** -/
theorem solution {ι : Type*}
    (H : ι → Ω → ℝ → ℝ) (hm : ∀ i, Measurable (Function.uncurry (H i)))
    (hp : ∀ i, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H i))
    (hq : ∀ (i : ι) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (J : Finset ι) {T : ℝ} (hT : 0 < T) :
    ∃ (hms : Measurable (Function.uncurry fun ω u => ∑ i ∈ J, H i ω u))
      (hps : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω u => ∑ i ∈ J, H i ω u)
      (hqs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T',
        (‖∑ i ∈ J, H i ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω u => ∑ i ∈ J, H i ω u) hms hps hqs T
        =ᵐ[P] fun ω => ∑ i ∈ J,
          LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (H i) (hm i) (hp i) (hq i) T ω := by
  classical
  induction J using Finset.induction with
  | empty =>
    have hfun : (fun (ω : Ω) (u : ℝ) => ∑ i ∈ (∅ : Finset ι), H i ω u)
        = fun (_ : Ω) (_ : ℝ) => (0 : ℝ) := by
      funext ω u
      simp
    have hmz : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) := measurable_const
    have hpz : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ) :=
      LevyStochCalc.Probability.progressivelyMeasurable_zero ℱ
    have hqz : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ _u in Set.Icc (0 : ℝ) T',
        (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T' _
      simp
    have hqz' := LevyStochCalc.Brownian.Ito.energy_lt_top_congr (P := P) hfun.symm hqz
    refine ⟨hfun ▸ hmz, hfun ▸ hpz, hqz', ?_⟩
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun (hfun ▸ hmz) (hfun ▸ hpz) hqz'
      hmz hpz hqz T]
    filter_upwards [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_readable W ℱ hℱ hmz hpz hqz T] with ω hω
    simpa using hω
  | insert a J ha ih =>
    obtain ⟨hms, hps, hqs, hae⟩ := ih
    have hfun : (fun (ω : Ω) (u : ℝ) => ∑ i ∈ insert a J, H i ω u)
        = fun ω u => H a ω u + ∑ i ∈ J, H i ω u := by
      funext ω u
      exact Finset.sum_insert ha
    have hma : Measurable (Function.uncurry fun ω u => H a ω u + ∑ i ∈ J, H i ω u) :=
      (hm a).add hms
    have hpa : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
        fun ω u => H a ω u + ∑ i ∈ J, H i ω u := (hp a).add hps
    have hqa : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T',
        (‖H a ω u + ∑ i ∈ J, H i ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
      LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound_readable (fun ω u => LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul _ _) (hm a) hms
        (hq a) hqs
    have hqi := LevyStochCalc.Brownian.Ito.energy_lt_top_congr (P := P) hfun.symm hqa
    refine ⟨hfun ▸ hma, hfun ▸ hpa, hqi, ?_⟩
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun (hfun ▸ hma) (hfun ▸ hpa) hqi
      hma hpa hqa T]
    filter_upwards [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_add_readable W ℱ hℱ (hm a) hms (hp a) hps (hq a) hqs
      hma hpa hqa hT, hae] with ω hadd hsum
    rw [hadd, hsum, Finset.sum_insert ha]

-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:25:29.617104+00:00
-- url     : https://prove2.me/submissions/9b712b7f-024e-4a40-89a8-eb08449c8661

import Definitions.Def_KLSModular_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrement
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoOptionalStopping
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_stochasticIntegralBrownian_finsetSum_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_energy_lt_top_of_bound_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_mul_stochasticIntegralBrownian_indIoc_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_progressivelyMeasurable_mul_indIoc_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_indicator_Ioc_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_sub_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stopped_eq_sub_sum_readable

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
/-- The pointwise difference of two progressively measurable processes is progressively
measurable. -/
theorem LevyStochCalc.Probability.ProgressivelyMeasurable.sub {A B : Ω → ℝ → E} (hA : ProgressivelyMeasurable ℱ A)
    (hB : ProgressivelyMeasurable ℱ B) :
    ProgressivelyMeasurable ℱ fun ω s => A ω s - B ω s := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => A p.1 s - B p.1 s) p.2)
      = fun p : Ω × ℝ =>
        (Set.Iic t).indicator (A p.1) p.2 - (Set.Iic t).indicator (B p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, sub_zero]
  rw [key]
  exact (hA t).sub (hB t)
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
/-- The squared extended norm of a difference is dominated by twice the sum of the squares. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul (x y : ℝ) :
    (‖x - y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x + y)])
end Energy
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Indicator
theorem LevyStochCalc.Brownian.Ito.indIoc_le_one (a b : ℝ) (ω : Ω) (s : ℝ) : |indIoc Ω a b ω s| ≤ 1 := by
  unfold indIoc
  by_cases h : s ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
end Indicator
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoOptionalStopping.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
section Stopped
variable (τ : Ω → WithTop ℝ)
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem LevyStochCalc.Brownian.Ito.abs_hitInd_le_one (c : ℝ) (ω : Ω) : |hitInd τ c ω| ≤ 1 := by
  by_cases h : ω ∈ {ω | τ ω = ((c : ℝ) : WithTop ℝ)} <;> simp [hitInd, h]
theorem LevyStochCalc.Brownian.Ito.measurable_hitInd {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (c : ℝ) : Measurable (hitInd τ c) :=
  measurable_const.indicator (ℱ.le c _ (hτ.measurableSet_eq c))
theorem LevyStochCalc.Brownian.Ito.stronglyMeasurable_hitInd {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (c : ℝ) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ c) (hitInd τ c) := by
  letI : MeasurableSpace Ω := ℱ c
  exact (measurable_const.indicator (hτ.measurableSet_eq c)).stronglyMeasurable
theorem LevyStochCalc.Brownian.Ito.measurable_cutTerm {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) (c t : ℝ) :
    Measurable (Function.uncurry (cutTerm τ H c t)) := by
  have hind : Measurable fun p : Ω × ℝ => indIoc Ω c t p.1 p.2 := by
    simp only [indIoc]
    exact (measurable_const.indicator measurableSet_Ioc).comp measurable_snd
  exact (((measurable_hitInd τ hτ c).comp measurable_fst).mul hind).mul hm
theorem LevyStochCalc.Brownian.Ito.progressivelyMeasurable_cutTerm (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hp : Probability.ProgressivelyMeasurable ℱ H) {c t : ℝ} (hc : 0 ≤ c) (hct : c < t) :
    Probability.ProgressivelyMeasurable ℱ (cutTerm τ H c t) :=
  (progressivelyMeasurable_mul_indIoc_readable ℱ hc hct ⟨1, abs_hitInd_le_one τ c⟩
    (measurable_hitInd τ hτ c) (stronglyMeasurable_hitInd τ hτ c)).mul hp
omit [IsProbabilityMeasure P] in
theorem LevyStochCalc.Brownian.Ito.abs_cutTerm_le {H : Ω → ℝ → ℝ} (c t : ℝ) (ω : Ω) (s : ℝ) :
    |cutTerm τ H c t ω s| ≤ |H ω s| := by
  have h1 : |hitInd τ c ω| ≤ 1 := abs_hitInd_le_one τ c ω
  have h2 : |indIoc Ω c t ω s| ≤ 1 := indIoc_le_one c t ω s
  calc |cutTerm τ H c t ω s| = |hitInd τ c ω| * |indIoc Ω c t ω s| * |H ω s| := by
        rw [cutTerm, abs_mul, abs_mul]
    _ ≤ 1 * 1 * |H ω s| := by
        gcongr
    _ = |H ω s| := by ring
omit [IsProbabilityMeasure P] in
theorem LevyStochCalc.Brownian.Ito.measurable_indTerm {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H)) (c t : ℝ) :
    Measurable (Function.uncurry (indTerm H c t)) := by
  have hind : Measurable fun p : Ω × ℝ => indIoc Ω c t p.1 p.2 := by
    simp only [indIoc]
    exact (measurable_const.indicator measurableSet_Ioc).comp measurable_snd
  exact hind.mul hm
theorem LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indTerm (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {H : Ω → ℝ → ℝ} (hp : Probability.ProgressivelyMeasurable ℱ H) {c t : ℝ} (hc : 0 ≤ c)
    (hct : c < t) : Probability.ProgressivelyMeasurable ℱ (indTerm H c t) := by
  have hfun : (fun (ω : Ω) (s : ℝ) => (1 : ℝ) * indIoc Ω c t ω s)
      = fun ω s => indIoc Ω c t ω s := by
    funext ω s
    ring
  have h1 := progressivelyMeasurable_mul_indIoc_readable (Ω := Ω) ℱ hc hct
    (V := fun _ => (1 : ℝ)) ⟨1, fun ω => by simp⟩ measurable_const stronglyMeasurable_const
  exact (hfun ▸ h1).mul hp
omit [IsProbabilityMeasure P] in
theorem LevyStochCalc.Brownian.Ito.abs_indTerm_le {H : Ω → ℝ → ℝ} (c t : ℝ) (ω : Ω) (s : ℝ) :
    |indTerm H c t ω s| ≤ |H ω s| := by
  have h2 : |indIoc Ω c t ω s| ≤ 1 := indIoc_le_one c t ω s
  calc |indTerm H c t ω s| = |indIoc Ω c t ω s| * |H ω s| := by rw [indTerm, abs_mul]
    _ ≤ 1 * |H ω s| := by gcongr
    _ = |H ω s| := by ring
section Identity
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ in
/-- The window cut is invisible at the horizon. -/
theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indTerm_zero {t : ℝ} (ht : 0 < t) {K : Ω → ℝ → ℝ}
    (hmK : Measurable (Function.uncurry K)) (hpK : Probability.ProgressivelyMeasurable ℱ K)
    (hqK : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmW : Measurable (Function.uncurry (indTerm K 0 t)))
    (hpW : Probability.ProgressivelyMeasurable ℱ (indTerm K 0 t))
    (hqW : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indTerm K 0 t ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    stochasticIntegralBrownian W ℱ hℱ (indTerm K 0 t) hmW hpW hqW t
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK t := by
  filter_upwards [stochasticIntegralBrownian_indicator_Ioc_readable W ℱ hℱ K hmK hpK hqK
      (le_refl (0 : ℝ)) ht hmW hpW hqW ht,
    stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ K hmK hpK hqK (le_refl (0 : ℝ))]
    with ω hloc hz
  have hloc' : stochasticIntegralBrownian W ℱ hℱ (indTerm K 0 t) hmW hpW hqW t ω
      = stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK (min t t) ω
        - stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK (min 0 t) ω := hloc
  rw [hloc', min_self, min_eq_left ht.le, hz]
  simp
include hℱ in
/-- **Optional stopping for the Itô integral, for a stopping time of finite range.** -/
theorem solution
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) (J : Finset ℝ)
    (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Probability.stopped τ H)
        (LevyStochCalc.Probability.measurable_uncurry_stopped hτ hm)
        (LevyStochCalc.Probability.ProgressivelyMeasurable.stopped hτ hp)
        (LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ H ω s) hq) t
      =ᵐ[P] fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
        - ∑ c ∈ J, LevyStochCalc.Brownian.Ito.hitInd τ c ω * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq c ω) := by
  classical
  have hmS := LevyStochCalc.Probability.measurable_uncurry_stopped hτ hm
  have hpS := LevyStochCalc.Probability.ProgressivelyMeasurable.stopped hτ hp
  have hqS := LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P) (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ H ω s) hq
  have hmI0 := LevyStochCalc.Brownian.Ito.measurable_indTerm hm 0 t
  have hpI0 := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indTerm ℱ hp (le_refl (0 : ℝ)) ht
  have hqI0 := LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P) (fun ω s => LevyStochCalc.Brownian.Ito.abs_indTerm_le (H := H) 0 t ω s) hq
  have hmW := LevyStochCalc.Brownian.Ito.measurable_indTerm hmS 0 t
  have hpW := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indTerm ℱ hpS (le_refl (0 : ℝ)) ht
  have hqW := LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P)
    (fun ω s => LevyStochCalc.Brownian.Ito.abs_indTerm_le (H := LevyStochCalc.Probability.stopped τ H) 0 t ω s) hqS
  set ι := {c : ℝ // c ∈ J} with hι
  have hmF : ∀ i : ι, Measurable (Function.uncurry (LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t)) :=
    fun i => LevyStochCalc.Brownian.Ito.measurable_cutTerm τ hτ hm i.1 t
  have hpF : ∀ i : ι, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t) :=
    fun i => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_cutTerm τ ℱ hτ hp (hJ0 i.1 i.2) (hJt i.1 i.2)
  have hqF : ∀ (i : ι) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun i => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P)
      (fun ω s => LevyStochCalc.Brownian.Ito.abs_cutTerm_le τ (H := H) i.1 t ω s) hq
  obtain ⟨hmSum, hpSum, hqSum, hSum⟩ := LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum_readable W ℱ hℱ
    (fun i : ι => LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t) hmF hpF hqF (Finset.univ : Finset ι) ht
  have hmD : Measurable (Function.uncurry fun ω u =>
      LevyStochCalc.Brownian.Ito.indTerm H 0 t ω u - ∑ i : ι, LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t ω u) := hmI0.sub hmSum
  have hpD : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      (fun ω u => LevyStochCalc.Brownian.Ito.indTerm H 0 t ω u - ∑ i : ι, LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t ω u) := hpI0.sub hpSum
  have hqD : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Brownian.Ito.indTerm H 0 t ω u - ∑ i : ι, LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound_readable (fun ω u => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hmI0 hmSum
      hqI0 hqSum
  have hpath : LevyStochCalc.Brownian.Ito.indTerm (LevyStochCalc.Probability.stopped τ H) 0 t
      = fun ω u => LevyStochCalc.Brownian.Ito.indTerm H 0 t ω u - ∑ i : ι, LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t ω u := by
    rw [LevyStochCalc.Brownian.Ito.stopped_eq_sub_sum_readable τ H J hJ0 hJt hτJ]
    funext ω u
    congr 1
    exact (Finset.sum_coe_sort J fun c => LevyStochCalc.Brownian.Ito.cutTerm τ H c t ω u).symm
  have hterm : ∀ i : ι,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t) (hmF i) (hpF i) (hqF i) t
        =ᵐ[P] fun ω => LevyStochCalc.Brownian.Ito.hitInd τ i.1 ω
          * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq i.1 ω) := by
    intro i
    have hc0 : 0 ≤ i.1 := hJ0 i.1 i.2
    have hct : i.1 < t := hJt i.1 i.2
    have hmIc := LevyStochCalc.Brownian.Ito.measurable_indTerm hm i.1 t
    have hpIc := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indTerm ℱ hp hc0 hct
    have hqIc := LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P)
      (fun ω s => LevyStochCalc.Brownian.Ito.abs_indTerm_le (H := H) i.1 t ω s) hq
    have hpull := LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_indIoc_readable W ℱ hℱ hc0 hct
      (V := LevyStochCalc.Brownian.Ito.hitInd τ i.1) ⟨1, LevyStochCalc.Brownian.Ito.abs_hitInd_le_one τ i.1⟩ (LevyStochCalc.Brownian.Ito.measurable_hitInd τ hτ i.1)
      (LevyStochCalc.Brownian.Ito.stronglyMeasurable_hitInd τ hτ i.1) H hm hp hq hmIc hpIc hqIc
      (hmF i) (hpF i) (hqF i) ht
    have hloc := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc_readable W ℱ hℱ H hm hp hq hc0 hct
      hmIc hpIc hqIc ht
    filter_upwards [hpull, hloc] with ω hpullω hlocω
    have hpull' : LevyStochCalc.Brownian.Ito.hitInd τ i.1 ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Brownian.Ito.indTerm H i.1 t) hmIc hpIc hqIc t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t) (hmF i) (hpF i) (hqF i) t ω :=
      hpullω
    have hloc' : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Brownian.Ito.indTerm H i.1 t) hmIc hpIc hqIc t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min t t) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min i.1 t) ω := hlocω
    rw [← hpull', hloc', min_self, min_eq_left hct.le]
  have hstep := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indTerm_zero W ℱ hℱ ht hmS hpS hqS hmW hpW hqW
  have hcongr := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hpath hmW hpW hqW hmD hpD hqD t
  have hsub := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sub_readable W ℱ hℱ hmI0 hmSum hpI0 hpSum hqI0 hqSum
    hmD hpD hqD ht
  have hI0 := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indTerm_zero W ℱ hℱ ht hm hp hq hmI0 hpI0 hqI0
  have hall : ∀ᵐ ω ∂P, ∀ i : ι,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t) (hmF i) (hpF i) (hqF i) t ω
        = LevyStochCalc.Brownian.Ito.hitInd τ i.1 ω * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq i.1 ω) :=
    MeasureTheory.ae_all_iff.mpr hterm
  filter_upwards [hstep, hsub, hI0, hSum, hall] with ω h1 h3 h4 h5 h6
  have h2 := congrFun hcongr ω
  rw [← h1, h2, h3, h4, h5, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => h6 i,
    Finset.sum_coe_sort J fun c => LevyStochCalc.Brownian.Ito.hitInd τ c ω
      * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq c ω)]

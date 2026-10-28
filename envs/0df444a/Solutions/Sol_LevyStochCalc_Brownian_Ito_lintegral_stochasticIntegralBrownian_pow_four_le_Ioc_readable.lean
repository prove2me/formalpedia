-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le_Ioc_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:25:19.684067+00:00
-- url     : https://prove2.me/submissions/d9b82019-e95b-449e-9654-13bf97a6c862

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentPartialSums
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentLintegral
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentRestrict
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentBounds
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_exists_restrict_Ioc_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_integral_partialSum_pow_four_le_varClock_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_lintegral_eval_sq_lt_top_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_lintegral_pow_four_eq_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_varClock_le_Ioc_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_abs_clamp_sub_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_comp_sum_ite_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_eval_simple_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A simple integrand is jointly measurable in the form the integral consumes. -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.measurable_uncurry_eval {T : ℝ} (G : SimplePredictable Ω T) :
    Measurable (Function.uncurry fun ω s => G.eval s ω) := G.eval_jointly_measurable
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraProduct.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section SimpleVsGeneral
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include hℱ h_adapt in
/-- **Difference isometry between an elementary integral and an `L²` integral.** -/
theorem LevyStochCalc.Brownian.Ito.isometry_simple_sub_stochasticIntegralBrownian {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖simpleIntegral W G T ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖G.eval s ω - H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hiso := isometry_diff_stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) H
    G.measurable_uncurry_eval hm (G.progressivelyMeasurable_eval ℱ h_adapt) hp
    (G.lintegral_eval_sq_lt_top_readable P) hq hT
  rw [← hiso]
  refine lintegral_congr_ae ?_
  filter_upwards [stochasticIntegralBrownian_eval_simple_readable W ℱ hℱ G h_adapt
    G.measurable_uncurry_eval (G.progressivelyMeasurable_eval ℱ h_adapt)
    (G.lintegral_eval_sq_lt_top_readable P) hT.le] with ω hω
  rw [hω]
end SimpleVsGeneral
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
section
variable {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.partialSum_card (ω : Ω) : G.partialSum W G.N ω = simpleIntegral W G T ω := by
  rw [simpleIntegral_eq_sum, partialSum, ← Fin.sum_univ_eq_sum_range
    (fun i => G.term W i ω) G.N]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [term, dif_pos i.isLt]
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_nonneg (c : Fin G.N → ℝ) (k : ℕ) : 0 ≤ G.varClock c k := by
  unfold varClock
  refine Finset.sum_nonneg fun j _ => ?_
  by_cases h : j < G.N
  · rw [dif_pos h]
    exact mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le)
  · rw [dif_neg h]
end
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section
variable {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
section Moments
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
include hℱ h_adapt hC0 hC in
/-- **Fourth-moment bound for the elementary integral against a per-tile coefficient
bound.** -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.integral_simpleIntegral_pow_four_le_varClock {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ (6 + gaussianFourthMoment) * G.varClock c G.N ^ 2 := by
  have hcard := G.integral_partialSum_pow_four_le_varClock_readable W ℱ hℱ h_adapt hC0 hC hc G.N le_rfl
  have hfun : ∀ ω, G.partialSum W G.N ω = simpleIntegral W G T ω := G.partialSum_card W
  simp_rw [hfun] at hcard
  calc ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ 6 * (G.varClock c G.N * G.varClock c G.N)
        + gaussianFourthMoment * G.varClock c G.N ^ 2 := hcard
    _ = (6 + gaussianFourthMoment) * G.varClock c G.N ^ 2 := by ring
end Moments
end
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.abs_truncate_xi_le {T : ℝ} (G : SimplePredictable Ω T) {C : ℝ}
    (hC : 0 ≤ C) (i : Fin G.N) (ω : Ω) : |(G.truncate C).ξ i ω| ≤ C := by
  refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.truncate_eval {T : ℝ} (G : SimplePredictable Ω T) {C : ℝ}
    (hC : 0 ≤ C) (s : ℝ) (ω : Ω) :
    (G.truncate C).eval s ω = max (-C) (min C (G.eval s ω)) := by
  have hg0 : max (-C) (min C (0 : ℝ)) = 0 := by
    rw [min_eq_right hC, max_eq_right (by linarith : -C ≤ (0 : ℝ))]
  exact (comp_sum_ite_readable G.partition_strictMono (fun i => G.ξ i ω) s
    (fun x => max (-C) (min C x)) hg0).symm
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.truncate_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (G : SimplePredictable Ω T) (C : ℝ)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i)) :
    ∀ i : Fin (G.truncate C).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((G.truncate C).partition i.castSucc)) ((G.truncate C).ξ i) := by
  intro i
  exact (measurable_const.max
    (measurable_const.min (h_adapt i).measurable)).stronglyMeasurable
section LintegralForm
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ in
/-- The fourth-moment bound against a per-tile coefficient bound, in `lintegral` form. -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_simpleIntegral_pow_four_le_varClock {T : ℝ}
    (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    {c : Fin G.N → ℝ} (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∫⁻ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * G.varClock c G.N ^ 2) := by
  rw [G.lintegral_pow_four_eq_readable W hC]
  exact ENNReal.ofReal_le_ofReal
    (G.integral_simpleIntegral_pow_four_le_varClock W ℱ hℱ h_adapt hC0 hC hc)
end LintegralForm
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A simple integrand whose coefficients vanish on every tile not contained in `(a, b]` has the
same elementary integral at every time past `b`. -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.simpleIntegral_eq_of_support
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {a b : ℝ}
    (hz : ∀ (j : Fin H.N) (ω : Ω),
      ¬(a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b) → H.ξ j ω = 0)
    {t : ℝ} (hbt : b ≤ t) (ω : Ω) : simpleIntegral W H t ω = simpleIntegral W H T ω := by
  rw [simpleIntegral_eq_sum]
  unfold simpleIntegral
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b
  · have h1 : H.partition j.succ ≤ t := hj.2.trans hbt
    have h2 : H.partition j.castSucc ≤ t :=
      ((H.partition_strictMono Fin.castSucc_lt_succ).le).trans h1
    rw [min_eq_left h1, min_eq_left h2]
  · rw [hz j ω hj, zero_mul, zero_mul]
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section IncrementBound
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ in
/-- **Fourth-moment bound for the `L²` Itô integral of an integrand supported in `(a, b]`.**
The bound sees only the length of the support. -/
theorem solution
    (F : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry F))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ F)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCF : ∀ ω s, |F ω s| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hsupp : ∀ ω s, s ∉ Set.Ioc a b → F ω s = 0) :
    ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by
  classical
  have hb : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  choose G0 hG0adapt hG0within using fun n : ℕ =>
    LevyStochCalc.Brownian.Ito.exists_adaptedSimple_within ℱ F hm hp hb (hq b hb)
      (show (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ from ENNReal.inv_pos.mpr
        (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩))
  have hGadapt : ∀ n, ∀ i : Fin ((G0 n).truncate C).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (((G0 n).truncate C).partition i.castSucc)) (((G0 n).truncate C).ξ i) :=
    fun n => LevyStochCalc.Brownian.Ito.SimplePredictable.truncate_adapt ℱ (G0 n) C (hG0adapt n)
  have hGbdd : ∀ n, ∀ (i : Fin ((G0 n).truncate C).N) (ω : Ω),
      |((G0 n).truncate C).ξ i ω| ≤ C := fun n i ω => (G0 n).abs_truncate_xi_le hC0 i ω
  choose T3 Q hQadapt hQeval hQxi using fun n : ℕ =>
    LevyStochCalc.Brownian.Ito.SimplePredictable.exists_restrict_Ioc_readable W ℱ ((G0 n).truncate C) (hGadapt n) hC0
      (hGbdd n) ha hab
  -- the restricted approximants are bounded by `C` and vanish off `(a, b]`
  have hQC : ∀ (n : ℕ) (j : Fin (Q n).N) (ω : Ω), |(Q n).ξ j ω| ≤ C := by
    intro n j ω
    refine (hQxi n j ω).trans ?_
    by_cases h : a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b
    · rw [if_pos h]
    · rw [if_neg h]; exact hC0
  have hQz : ∀ (n : ℕ) (j : Fin (Q n).N) (ω : Ω),
      ¬(a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b) → (Q n).ξ j ω = 0 := by
    intro n j ω h
    have := (hQxi n j ω).trans (le_of_eq (if_neg h))
    exact abs_nonpos_iff.mp this
  -- their elementary integrals at `b` are the ones the variance budget bounds
  have hQsimp : ∀ (n : ℕ) (ω : Ω),
      LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω = LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) (T3 n) ω :=
    fun n ω => (Q n).simpleIntegral_eq_of_support W (hQz n) le_rfl ω
  have hQbound : ∀ n : ℕ, ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by
    intro n
    simp_rw [hQsimp n]
    refine le_trans ((Q n).lintegral_simpleIntegral_pow_four_le_varClock W ℱ hℱ (hQadapt n)
      hC0 (hQC n) (c := fun j => if a ≤ (Q n).partition j.castSucc
        ∧ (Q n).partition j.succ ≤ b then C else 0) (hQxi n)) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hV := (Q n).varClock_le_Ioc_readable (a := a) (b := b) (C := C) hab.le
    have hV0 := (Q n).varClock_nonneg
      (fun j => if a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b then C else 0)
      (Q n).N
    have hcg : (0 : ℝ) ≤ 6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment := by
      linarith [LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg]
    have hsq : (Q n).varClock
        (fun j => if a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b then C else 0)
        (Q n).N ^ 2 ≤ (C ^ 2 * (b - a)) ^ 2 := by
      nlinarith [hV, hV0]
    calc (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (Q n).varClock
            (fun j => if a ≤ (Q n).partition j.castSucc
              ∧ (Q n).partition j.succ ≤ b then C else 0) (Q n).N ^ 2
        ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 2 * (b - a)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hcg
      _ = (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by ring
  -- the restricted approximants still approximate `F`
  have hQwithin : ∀ n : ℕ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖(Q n).eval s ω - F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    refine le_trans ?_ (hG0within n).le
    refine lintegral_mono fun ω => lintegral_mono fun s => ?_
    have hle : ‖(Q n).eval s ω - F ω s‖₊ ≤ ‖F ω s - (G0 n).eval s ω‖₊ := by
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm, Real.norm_eq_abs]
      have hstep : |(Q n).eval s ω - F ω s|
          ≤ |((G0 n).truncate C).eval s ω - F ω s| := by
        rw [hQeval n s ω]
        by_cases hs : s ∈ Set.Ioc a b
        · rw [Set.indicator_of_mem hs]
          simp
        · rw [Set.indicator_of_notMem hs, zero_mul, hsupp ω s hs]
          simp
      refine hstep.trans ?_
      rw [(G0 n).truncate_eval hC0 s ω, abs_sub_comm (F ω s)]
      exact LevyStochCalc.Brownian.Ito.abs_clamp_sub_le_readable hC0 (hCF ω s)
    exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr hle) 2
  have htol : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
    have h := ENNReal.tendsto_inv_nat_nhds_zero.comp hg
    refine h.congr fun n => ?_
    simp [Nat.cast_add_one]
  have hsq : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htol
      (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall fun n => ?_)
    rw [LevyStochCalc.Brownian.Ito.isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ (Q n) (hQadapt n) F hm hp hq hb]
    exact hQwithin n
  have heL : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
      (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω) 2 P) Filter.atTop (nhds 0) := by
    have hrw : ∀ n, MeasureTheory.eLpNorm
        (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω) 2 P
        = (∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
              ^ ((2 : ℝ))⁻¹ := by
      intro n
      rw [← LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq]
      exact (ENNReal.rpow_rpow_inv (by norm_num) _).symm
    simp_rw [hrw]
    have h := (ENNReal.continuous_rpow_const (y := ((2 : ℝ))⁻¹)).tendsto 0 |>.comp hsq
    simpa [Function.comp_def,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < ((2 : ℝ))⁻¹)] using h
  have hmeasG : ∀ n, Measurable (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω) := by
    intro n
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((Q n).ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hmeasSI : Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b) :=
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ F hm hp hq b).mono (ℱ.le b)).measurable
  have hTIM : MeasureTheory.TendstoInMeasure P
      (fun n ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω) Filter.atTop
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun n => (hmeasG n).aestronglyMeasurable) hmeasSI.aestronglyMeasurable heL
  obtain ⟨ns, -, hns_ae⟩ := hTIM.exists_seq_tendsto_ae
  have hcont : Continuous fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 4 := by
    have hfun : (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 4)
        = fun x : ℝ => ((‖x‖₊ ^ 4 : ℝ≥0) : ℝ≥0∞) := by
      funext x; rw [ENNReal.coe_pow]
    rw [hfun]
    exact ENNReal.continuous_coe.comp (continuous_nnnorm.pow 4)
  have hfatou : ∫⁻ ω,
      (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ Filter.liminf (fun k => ∫⁻ ω,
        (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q (ns k)) b ω‖₊ : ℝ≥0∞) ^ 4 ∂P) Filter.atTop := by
    have h1 : ∀ᵐ ω ∂P,
        (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4
        = Filter.liminf (fun k =>
            (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q (ns k)) b ω‖₊ : ℝ≥0∞) ^ 4) Filter.atTop := by
      filter_upwards [hns_ae] with ω hω
      exact ((hcont.tendsto _).comp hω).liminf_eq.symm
    rw [lintegral_congr_ae h1]
    exact lintegral_liminf_le fun k => (hcont.measurable.comp (hmeasG (ns k)))
  exact hfatou.trans (Filter.liminf_le_of_frequently_le
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun k => hQbound (ns k))))

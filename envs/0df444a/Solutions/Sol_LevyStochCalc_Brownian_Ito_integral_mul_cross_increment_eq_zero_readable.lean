-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_mul_cross_increment_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:29:14.711981+00:00
-- url     : https://prove2.me/submissions/1f57e522-05eb-49e2-afbe-65ca63aec66e

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossVariation
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_integralAgainst_readable
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_stochasticIntegral_mul_eq_zero_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossVariation.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
section TwoCell
theorem LevyStochCalc.Brownian.Ito.twoCell_integralAgainst {a b : ℝ} (ha : 0 < a) (hab : a < b) (Z : Ω → ℝ)
    (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) (Y : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (twoCell ha hab Z hZm hZb).integralAgainst Y t ω
      = Z ω * (Y (min b t) ω - Y (min a t) ω) := by
  change (∑ i : Fin 2, (![fun _ : Ω => (0 : ℝ), Z] : Fin 2 → Ω → ℝ) i ω
      * (Y (min ((![0, a, b] : Fin 3 → ℝ) i.succ) t) ω
        - Y (min ((![0, a, b] : Fin 3 → ℝ) i.castSucc) t) ω))
    = Z ω * (Y (min b t) ω - Y (min a t) ω)
  rw [Fin.sum_univ_two]
  simp
theorem LevyStochCalc.Brownian.Ito.oneCell_integralAgainst {b : ℝ} (hb : 0 < b) (Z : Ω → ℝ)
    (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) (Y : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (oneCell hb Z hZm hZb).integralAgainst Y t ω
      = Z ω * (Y (min b t) ω - Y (min 0 t) ω) := by
  change (∑ i : Fin 1, (![Z] : Fin 1 → Ω → ℝ) i ω
      * (Y (min ((![0, b] : Fin 2 → ℝ) i.succ) t) ω
        - Y (min ((![0, b] : Fin 2 → ℝ) i.castSucc) t) ω))
    = Z ω * (Y (min b t) ω - Y (min 0 t) ω)
  rw [Fin.sum_univ_one]
  simp
end TwoCell
section PullOut
variable (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
/-- **A weight known at the left endpoint comes inside the integral.** For `Z` bounded and
measurable for `ℱ a`, the weighted increment of an Itô integral over `(a, b]` is the Itô integral
of `Z` carried on that cell against the integrand. -/
theorem LevyStochCalc.Brownian.Ito.mul_sub_stochasticIntegralBrownian_ae {a b : ℝ} (ha : 0 < a) (hab : a < b) {Z : Ω → ℝ}
    (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M)
    (hZa : StronglyMeasurable[ℱ a] Z) {t : ℝ} (hbt : b ≤ t) :
    (fun ω => Z ω * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω))
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (twoCell ha hab Z hZm hZb).eval s ω * H ω s)
        ((twoCell ha hab Z hZm hZb).measurable_uncurry_eval_mul hm)
        ((twoCell ha hab Z hZm hZb).progressivelyMeasurable_eval_mul ℱ
          (twoCell_adapted ha hab hZm hZb hZa) hp)
        ((twoCell ha hab Z hZm hZb).lintegral_eval_mul_sq_lt_top hq) t := by
  have ht : 0 < t := lt_of_lt_of_le (ha.trans hab) hbt
  have hkey := stochasticIntegralBrownian_integralAgainst_readable W ℱ hℱ (twoCell ha hab Z hZm hZb)
    (twoCell_adapted ha hab hZm hZb hZa) H hm hp hq
    ((twoCell ha hab Z hZm hZb).measurable_uncurry_eval_mul hm)
    ((twoCell ha hab Z hZm hZb).progressivelyMeasurable_eval_mul ℱ
      (twoCell_adapted ha hab hZm hZb hZa) hp)
    ((twoCell ha hab Z hZm hZb).lintegral_eval_mul_sq_lt_top hq) ht
  refine Filter.EventuallyEq.trans ?_ hkey
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [twoCell_integralAgainst, min_eq_left hbt, min_eq_left (le_trans hab.le hbt)]
/-- The pull-out at the left end of the horizon, where the cell is `(0, b]`. -/
theorem LevyStochCalc.Brownian.Ito.mul_sub_stochasticIntegralBrownian_ae_zero {b : ℝ} (hb : 0 < b) {Z : Ω → ℝ}
    (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M)
    (hZ0 : StronglyMeasurable[ℱ 0] Z) {t : ℝ} (hbt : b ≤ t) :
    (fun ω => Z ω * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq 0 ω))
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (oneCell hb Z hZm hZb).eval s ω * H ω s)
        ((oneCell hb Z hZm hZb).measurable_uncurry_eval_mul hm)
        ((oneCell hb Z hZm hZb).progressivelyMeasurable_eval_mul ℱ
          (oneCell_adapted hb hZm hZb hZ0) hp)
        ((oneCell hb Z hZm hZb).lintegral_eval_mul_sq_lt_top hq) t := by
  have ht : 0 < t := lt_of_lt_of_le hb hbt
  have hkey := stochasticIntegralBrownian_integralAgainst_readable W ℱ hℱ (oneCell hb Z hZm hZb)
    (oneCell_adapted hb hZm hZb hZ0) H hm hp hq
    ((oneCell hb Z hZm hZb).measurable_uncurry_eval_mul hm)
    ((oneCell hb Z hZm hZb).progressivelyMeasurable_eval_mul ℱ
      (oneCell_adapted hb hZm hZb hZ0) hp)
    ((oneCell hb Z hZm hZb).lintegral_eval_mul_sq_lt_top hq) ht
  refine Filter.EventuallyEq.trans ?_ hkey
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [oneCell_integralAgainst, min_eq_left hbt, min_eq_left ht.le]
/-- **The weighted increment of an Itô integral is an Itô integral.** For `Z` bounded and
measurable for `ℱ a`, some admissible integrand has `Z · (M_b − M_a)` as its integral. -/
theorem LevyStochCalc.Brownian.Ito.exists_pullout_mul_sub_stochasticIntegralBrownian {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℝ} (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M)
    (hZa : StronglyMeasurable[ℱ a] Z) {t : ℝ} (hbt : b ≤ t) :
    ∃ (G : Ω → ℝ → ℝ) (hGm : Measurable (Function.uncurry G))
      (hGp : Probability.ProgressivelyMeasurable ℱ G)
      (hGs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      (fun ω => Z ω * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω))
        =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ G hGm hGp hGs t := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · exact ⟨_, _, _, _,
      mul_sub_stochasticIntegralBrownian_ae_zero W hℱ H hm hp hq hab hZm hZb hZa hbt⟩
  · exact ⟨_, _, _, _,
      mul_sub_stochasticIntegralBrownian_ae W hℱ H hm hp hq ha' hab hZm hZb hZa hbt⟩
end PullOut
section Cross
open LevyStochCalc.Brownian.Multidim
variable {d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
/-- **The cross-variation pairs to zero against a weight known at the left endpoint.** For
distinct coordinates, the product of the increments of the two Itô integrals over a cell is
orthogonal to every bounded weight measurable at the cell's left endpoint. -/
theorem solution {i j : Fin d} (hij : i ≠ j) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) {Z : Ω → ℝ} (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M)
    (hZa : StronglyMeasurable[ℱ a] Z) :
    ∫ ω, Z ω * ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω)) ∂P = 0 := by
  have ht : (0 : ℝ) ≤ b := le_trans ha hab.le
  have hone : ∀ _ω : Ω, |(1 : ℝ)| ≤ 1 := fun _ => le_of_eq abs_one
  obtain ⟨G, hGm, hGp, hGs, h1⟩ := LevyStochCalc.Brownian.Ito.exists_pullout_mul_sub_stochasticIntegralBrownian
    (W.W i) (hcoord i) H hHm hHp hHs ha hab hZm hZb hZa (le_refl b)
  obtain ⟨G', hGm', hGp', hGs', h2⟩ := LevyStochCalc.Brownian.Ito.exists_pullout_mul_sub_stochasticIntegralBrownian
    (W.W j) (hcoord j) K hKm hKp hKs ha hab (Z := fun _ => (1 : ℝ)) measurable_const hone
    stronglyMeasurable_const (le_refl b)
  have hcross := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_stochasticIntegral_mul_eq_zero_readable W hij hcoord
    hGm hGp hGs hGm' hGp' hGs' ht
  simp only [LevyStochCalc.Brownian.Ito.stochasticIntegral] at hcross
  refine Eq.trans ?_ hcross
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with ω e1 e2
  simp only [one_mul] at e2
  rw [← e1, ← e2]
  ring

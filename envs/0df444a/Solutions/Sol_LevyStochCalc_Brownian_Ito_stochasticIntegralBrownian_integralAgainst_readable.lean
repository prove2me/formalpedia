-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:19:26.105981+00:00
-- url     : https://prove2.me/submissions/baf5a850-0231-4afb-ac57-dd32edc54fbd

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_exists_mul_simple_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_lintegral_eval_sq_lt_top_readable
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

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
private lemma LevyStochCalc.Brownian.Ito.eLpNorm_mul_le_of_bound {P : Measure Ω} {c g : Ω → ℝ} {M : ℝ}
    (hM : ∀ ω, |c ω| ≤ M) :
    MeasureTheory.eLpNorm (fun ω => c ω * g ω) 2 P
      ≤ (‖M‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm g 2 P := by
  have hsm : (fun ω => M * g ω) = (M • g : Ω → ℝ) := by funext ω; simp
  refine le_trans (MeasureTheory.eLpNorm_mono (g := fun ω => M * g ω) fun ω => ?_) ?_
  · have hM0 : 0 ≤ M := (abs_nonneg (c ω)).trans (hM ω)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hM0]
    exact mul_le_mul_of_nonneg_right (hM ω) (abs_nonneg _)
  · rw [hsm]; exact MeasureTheory.eLpNorm_const_smul_le
section Associativity
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hmm : Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s))
  (hmp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s)
  (hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include hℱ h_adapt in
/-- **Associativity against a simple integrand.** Summing the increments of the `L²` Itô integral
of `H` against the coefficients of a simple integrand `G` gives the `L²` Itô integral of the
product `G · H`. -/
theorem solution {t : ℝ} (ht : 0 < t) :
    G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t
      =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
        hmm hmp hmq t := by
  classical
  obtain ⟨B, hB0, hB⟩ := G.exists_eval_bound
  choose Th Q hQadapt hQeval hQint using fun n : ℕ =>
    LevyStochCalc.Brownian.Ito.SimplePredictable.exists_mul_simple_readable W ℱ G (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) h_adapt
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H hm hp hq n)
  choose Mb hMb using G.ξ_bounded
  -- measurability bookkeeping
  have hMmeas : ∀ u : ℝ, Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u) :=
    fun u => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq u).mono
      (ℱ.le u)).measurable
  have hInmeas : ∀ (n : ℕ) (u : ℝ),
      Measurable (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) u) := by
    intro n u
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _))
  have hQmeas : ∀ n : ℕ, Measurable (LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t) := by
    intro n
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((Q n).ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hIAmeas : Measurable (G.integralAgainst
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t) := by
    unfold LevyStochCalc.Brownian.Ito.SimplePredictable.integralAgainst
    exact Finset.measurable_sum _ fun i _ =>
      (G.ξ_measurable i).mul ((hMmeas _).sub (hMmeas _))
  have hconv : ∀ g : Ω → ℝ, MeasureTheory.eLpNorm g 2 P * MeasureTheory.eLpNorm g 2 P
      = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro g
    rw [← LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  -- (d) the product elementary integrals converge to the `L²` integral of `G.eval · H`
  have hd : Filter.Tendsto (fun n => ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    have hbd : ∀ s ω, (‖G.eval s ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal B := by
      intro s ω
      calc (‖G.eval s ω‖₊ : ℝ≥0∞)
          = ENNReal.ofReal ‖G.eval s ω‖ := by
            rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
        _ ≤ ENNReal.ofReal B :=
            ENNReal.ofReal_le_ofReal ((Real.norm_eq_abs _).le.trans (hB s ω))
    have hne : ENNReal.ofReal B ^ 2 ≠ ⊤ := (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
    have hkey : ∀ n, ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
            hmm hmp hmq t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
        ≤ ENNReal.ofReal B ^ 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P := by
      intro n
      rw [LevyStochCalc.Brownian.Ito.isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ (Q n) (hQadapt n)
        (fun ω s => G.eval s ω * H ω s) hmm hmp hmq ht,
        ← MeasureTheory.lintegral_const_mul' _ _ hne]
      refine lintegral_mono fun ω => ?_
      rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
      refine lintegral_mono fun s => ?_
      have hrw : (Q n).eval s ω - G.eval s ω * H ω s
          = G.eval s ω * -(H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n).eval s ω) := by
        rw [hQeval n s ω]; ring
      rw [hrw, nnnorm_mul, nnnorm_neg, ENNReal.coe_mul, mul_pow]
      gcongr
      exact hbd s ω
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Filter.Eventually.of_forall fun n => bot_le) (Filter.Eventually.of_forall hkey)
    have hml := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal B ^ 2)
      (LevyStochCalc.Brownian.Ito.masterApprox_eval_tendsto (t := t) ℱ H hm hp hq) (Or.inr hne)
    simpa using hml
  -- (e) the product elementary integrals converge to the integral against the `L²` integral
  have hu_nn : ∀ i : Fin G.N, 0 ≤ min (G.partition i.succ) t :=
    fun i => le_min (G.partition_nonneg _) ht.le
  have hu_nn' : ∀ i : Fin G.N, 0 ≤ min (G.partition i.castSucc) t :=
    fun i => le_min (G.partition_nonneg _) ht.le
  have hstep : ∀ n : ℕ, (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
      - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω)
      = ∑ i : Fin G.N,
        ((fun ω => G.ξ i ω * (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n)
            (min (G.partition i.succ) t) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω))
        - (fun ω => G.ξ i ω * (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n)
            (min (G.partition i.castSucc) t) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
              (min (G.partition i.castSucc) t) ω))) := by
    intro n
    funext ω
    simp only [Finset.sum_apply, Pi.sub_apply]
    rw [← hQint n t ω]
    unfold LevyStochCalc.Brownian.Ito.SimplePredictable.integralAgainst
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbound : ∀ n : ℕ, MeasureTheory.eLpNorm (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
      - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω) 2 P
      ≤ ∑ i : Fin G.N, ((‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) (min (G.partition i.succ) t) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω) 2 P
        + (‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) (min (G.partition i.castSucc) t) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
                (min (G.partition i.castSucc) t) ω) 2 P) := by
    intro n
    have haesm : ∀ (i : Fin G.N) (u : ℝ), MeasureTheory.AEStronglyMeasurable
        (fun ω => G.ξ i ω * (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) u ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)) P :=
      fun i u => ((G.ξ_measurable i).mul ((hInmeas n u).sub (hMmeas u))).aestronglyMeasurable
    rw [hstep n]
    refine le_trans (MeasureTheory.eLpNorm_sum_le
      (fun i _ => (haesm i _).sub (haesm i _)) (by norm_num)) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (MeasureTheory.eLpNorm_sub_le (haesm i _) (haesm i _) (by norm_num)) ?_
    exact add_le_add (LevyStochCalc.Brownian.Ito.eLpNorm_mul_le_of_bound (hMb i)) (LevyStochCalc.Brownian.Ito.eLpNorm_mul_le_of_bound (hMb i))
  have hlim : Filter.Tendsto (fun n : ℕ =>
      ∑ i : Fin G.N, ((‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) (min (G.partition i.succ) t) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω) 2 P
        + (‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) (min (G.partition i.castSucc) t) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
                (min (G.partition i.castSucc) t) ω) 2 P)) Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ≥0∞) = ∑ _i : Fin G.N, (0 : ℝ≥0∞) := by simp
    rw [h0]
    refine tendsto_finsetSum _ fun i _ => ?_
    have h1 := ENNReal.Tendsto.const_mul (a := (‖Mb i‖₊ : ℝ≥0∞))
      (LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2 W ℱ hℱ H hm hp hq (hu_nn i)) (Or.inr ENNReal.coe_ne_top)
    have h2 := ENNReal.Tendsto.const_mul (a := (‖Mb i‖₊ : ℝ≥0∞))
      (LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2 W ℱ hℱ H hm hp hq (hu_nn' i)) (Or.inr ENNReal.coe_ne_top)
    simpa using h1.add h2
  have heL : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun ω =>
      LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
        - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω) 2 P)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall hbound)
  have he : Filter.Tendsto (fun n => ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
      - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    have h2 := ENNReal.Tendsto.mul heL (Or.inr (by simp)) heL (Or.inr (by simp))
    simpa [hconv] using h2
  -- squeeze the two limits together
  have hle : ∫⁻ ω,
      (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P ≤ 0 := by
    have hlim2 : Filter.Tendsto (fun n => 2 * ((∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
          - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
            : ℝ≥0∞) ^ 2 ∂P)
        + ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
              hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)) Filter.atTop (nhds 0) := by
      have h3 := ENNReal.Tendsto.const_mul (a := 2) (he.add hd) (Or.inr (by simp))
      simpa using h3
    refine ge_of_tendsto hlim2 (Filter.Eventually.of_forall fun n => ?_)
    have hm2 : AEMeasurable (fun ω => (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
        - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
          : ℝ≥0∞) ^ 2) P :=
      ((((hQmeas n).sub hIAmeas).nnnorm).coe_nnreal_ennreal).pow_const 2 |>.aemeasurable
    calc ∫⁻ ω, (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
              hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * ((‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
              - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
                : ℝ≥0∞) ^ 2
            + (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                  hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have hrw : G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
                - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                    hmm hmp hmq t ω
              = -(LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
                    - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω)
                + (LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
                    - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                        hmm hmp hmq t ω) := by ring
          rw [hrw]
          refine le_trans (LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul_brownian _ _) ?_
          rw [nnnorm_neg]
      _ = 2 * ((∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
              - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
                : ℝ≥0∞) ^ 2 ∂P)
            + ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                  hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) := by
          rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
            MeasureTheory.lintegral_add_left' hm2]
  have hzero : ∫⁻ ω,
      (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P = 0 := le_antisymm hle bot_le
  have hSIm : Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => G.eval s ω * H ω s) hmm hmp hmq t) :=
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
      hmm hmp hmq t).mono (ℱ.le t)).measurable
  have hmeas : Measurable fun ω =>
      (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
            hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 :=
    (((hIAmeas.sub hSIm).nnnorm).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hzero] with ω hω
  have h0 : (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa using hω
  simpa [sub_eq_zero] using h0

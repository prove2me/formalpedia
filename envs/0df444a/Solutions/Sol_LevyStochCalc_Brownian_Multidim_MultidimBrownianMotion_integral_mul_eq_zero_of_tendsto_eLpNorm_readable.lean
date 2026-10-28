-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_eq_zero_of_tendsto_eLpNorm_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:14:44.106132+00:00
-- url     : https://prove2.me/submissions/1ea76418-96cb-4609-ae03-2eb994b3fcd3

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}
section L2Limit
open LevyStochCalc.Brownian.Ito
omit [IsProbabilityMeasure P] in
/-- The `L²` inner product of two `Lp` representatives is the integral of their product. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.inner_toLp_eq_integral_mul {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (inner ℝ (hf.toLp f) (hg.toLp g) : ℝ) = ∫ ω, f ω * g ω ∂P := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [RCLike.inner_apply, h1, h2]
  simp [mul_comm]
omit [IsProbabilityMeasure P] in
/-- The `L²` pairing is continuous, so a pairing that vanishes along `L²`-convergent sequences
vanishes in the limit. -/
theorem solution {u v : Ω → ℝ} {un vn : ℕ → Ω → ℝ}
    (hu : MemLp u 2 P) (hv : MemLp v 2 P)
    (hun : ∀ n, MemLp (un n) 2 P) (hvn : ∀ n, MemLp (vn n) 2 P)
    (h0 : ∀ n, ∫ ω, un n ω * vn n ω ∂P = 0)
    (hcu : Filter.Tendsto (fun n => eLpNorm (fun ω => un n ω - u ω) 2 P) Filter.atTop (nhds 0))
    (hcv : Filter.Tendsto (fun n => eLpNorm (fun ω => vn n ω - v ω) 2 P) Filter.atTop (nhds 0)) :
    ∫ ω, u ω * v ω ∂P = 0 := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hUn : Filter.Tendsto (fun n => (hun n).toLp (un n)) Filter.atTop (nhds (hu.toLp u)) := by
    rw [MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm _ u hu]
    have heq : ∀ n, eLpNorm (⇑((hun n).toLp (un n)) - u) 2 P
        = eLpNorm (fun ω => un n ω - u ω) 2 P := by
      intro n
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hun n).coeFn_toLp] with ω h
      simp [h]
    simp_rw [heq]
    exact hcu
  have hVn : Filter.Tendsto (fun n => (hvn n).toLp (vn n)) Filter.atTop (nhds (hv.toLp v)) := by
    rw [MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm _ v hv]
    have heq : ∀ n, eLpNorm (⇑((hvn n).toLp (vn n)) - v) 2 P
        = eLpNorm (fun ω => vn n ω - v ω) 2 P := by
      intro n
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hvn n).coeFn_toLp] with ω h
      simp [h]
    simp_rw [heq]
    exact hcv
  have hinner : Filter.Tendsto
      (fun n => (inner ℝ ((hun n).toLp (un n)) ((hvn n).toLp (vn n)) : ℝ)) Filter.atTop
      (nhds (inner ℝ (hu.toLp u) (hv.toLp v) : ℝ)) := hUn.inner hVn
  have hzero : ∀ n, (inner ℝ ((hun n).toLp (un n)) ((hvn n).toLp (vn n)) : ℝ) = 0 := fun n => by
    rw [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.inner_toLp_eq_integral_mul (hun n) (hvn n)]; exact h0 n
  simp_rw [hzero] at hinner
  have hlim := tendsto_nhds_unique tendsto_const_nhds hinner
  rw [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.inner_toLp_eq_integral_mul hu hv] at hlim
  exact hlim.symm

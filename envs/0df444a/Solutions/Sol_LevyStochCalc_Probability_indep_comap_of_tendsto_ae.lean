-- Prove2me | solution 1 for LevyStochCalc.Probability.indep_comap_of_tendsto_ae
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:09:34.682575+00:00
-- url     : https://prove2.me/submissions/ef3c69b0-076d-41c9-9014-d6886cb48307

import Definitions.Def_LevyStochCalc_Probability_IndepLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Independence survives almost-everywhere limits

If each random variable `X n` is independent of a σ-algebra `m` and `X n → Y` almost
everywhere, then `Y` is independent of `m`: for a set `A ∈ m` the laws of `Y` under `P|_A` and
under `P(A) • P` have the same integrals against bounded continuous functions, by dominated
convergence, hence coincide.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace LevyStochCalc.Probability

variable {Ω 𝓧 : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [TopologicalSpace 𝓧] [MeasurableSpace 𝓧] [BorelSpace 𝓧] [HasOuterApproxClosed 𝓧]



theorem _root_.solution (hm : m ≤ mΩ) {X : ℕ → Ω → 𝓧}
    {Y : Ω → 𝓧} (hX : ∀ n, Measurable[mΩ] (X n)) (hY : Measurable[mΩ] Y)
    (hind : ∀ n, Indep m (MeasurableSpace.comap (X n) inferInstance) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Indep m (MeasurableSpace.comap Y inferInstance) P := by
  rw [Indep_iff]
  rintro A _ hA ⟨D, hD, rfl⟩
  have hA' : MeasurableSet[mΩ] A := hm _ hA
  have hint : ∀ f : 𝓧 →ᵇ ℝ, ∫ ω in A, f (Y ω) ∂P = (P A).toReal * ∫ ω, f (Y ω) ∂P := by
    intro f
    have hb : ∀ n, ∀ᵐ ω ∂P, ‖f (X n ω)‖ ≤ ‖f‖ := fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _
    have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => f (X n ω)) atTop (𝓝 (f (Y ω))) := by
      filter_upwards [hlim] with ω hω
      exact (f.continuous.tendsto _).comp hω
    have hmeas : ∀ n, AEStronglyMeasurable (fun ω => f (X n ω)) P := fun n =>
      (f.continuous.measurable.comp (hX n)).aestronglyMeasurable
    have h1 : Tendsto (fun n => ∫ ω, f (X n ω) ∂P) atTop (𝓝 (∫ ω, f (Y ω) ∂P)) :=
      tendsto_integral_of_dominated_convergence (fun _ => ‖f‖) hmeas (integrable_const _) hb hconv
    have h2 : Tendsto (fun n => ∫ ω in A, f (X n ω) ∂P) atTop (𝓝 (∫ ω in A, f (Y ω) ∂P)) :=
      tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun n => (hmeas n).restrict) (integrable_const _)
        (fun n => ae_restrict_of_ae (hb n)) (ae_restrict_of_ae hconv)
    have h3 : ∀ n, ∫ ω in A, f (X n ω) ∂P = (P A).toReal * ∫ ω, f (X n ω) ∂P := fun n =>
      setIntegral_eq_measure_mul_of_indep hm (hX n) (hind n) hA f
    simp_rw [h3] at h2
    exact tendsto_nhds_unique h2 (h1.const_mul _)
  have : IsFiniteMeasure ((P A) • P.map Y) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top (measure_lt_top P A) (measure_lt_top _ _)⟩
  have hmeq : (P.restrict A).map Y = (P A) • P.map Y := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [integral_map hY.aemeasurable f.continuous.aestronglyMeasurable, integral_smul_measure,
      integral_map hY.aemeasurable f.continuous.aestronglyMeasurable, hint f, smul_eq_mul]
  have := congrArg (fun ν : Measure 𝓧 => ν D) hmeq
  simp only [Measure.map_apply hY hD, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (hY hD)] at this
  rw [Set.inter_comm, this]

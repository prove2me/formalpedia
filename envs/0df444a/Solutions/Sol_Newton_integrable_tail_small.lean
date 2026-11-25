-- Prove2me | solution 1 for Newton.integrable_tail_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:00:25.140378+00:00
-- url     : https://prove2.me/submissions/fb047a98-9bc0-46e7-bf0a-dc9757445dbf

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense

set_option autoImplicit false
open MeasureTheory NNReal SchwartzMap
open scoped ENNReal ContDiff Topology
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f : (Fin n → ℝ) → ℂ)
    (hf : MemLp f 1 volume)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ R > 0, ∫ x, ‖f x‖ ∂(volume.restrict {x | R ≤ ‖x‖}) < ε := by
  set g : (Fin n → ℝ) → ℝ := fun x => ‖f x‖ with hg_def
  have hf_int : Integrable f volume :=
    (memLp_one_iff_integrable).1 hf
  have hg_integrable : Integrable g volume := by
    simpa [hg_def] using hf_int.norm
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x => norm_nonneg _
  let tail : ℕ → Set (Fin n → ℝ) := fun k => {x | (k : ℝ) ≤ ‖x‖}
  have h_tail_meas : ∀ k, MeasurableSet (tail k) := by
    intro k
    have h_closed :
        IsClosed {x : (Fin n → ℝ) | (k : ℝ) ≤ ‖x‖} :=
      (isClosed_le continuous_const continuous_norm)
    simpa [tail] using h_closed.measurableSet
  have h_tendsto :
      Filter.Tendsto
        (fun k : ℕ => ∫ x, Set.indicator (tail k) g x ∂volume)
        Filter.atTop (𝓝 (0 : ℝ)) := by
    have h_meas : ∀ k : ℕ,
        AEStronglyMeasurable (fun x => Set.indicator (tail k) g x) volume := by
      intro k
      exact hg_integrable.aestronglyMeasurable.indicator (h_tail_meas k)
    have h_bound : ∀ k : ℕ, ∀ᵐ x ∂volume,
        ‖Set.indicator (tail k) g x‖ ≤ g x := by
      intro k
      refine Filter.Eventually.of_forall ?_
      intro x
      by_cases hx : x ∈ tail k
      · have hx_nonneg : 0 ≤ g x := hg_nonneg x
        simp [tail, hx, hg_def]
      · simp [tail, hx, hg_def]
    have h_lim : ∀ᵐ x ∂volume,
        Filter.Tendsto (fun k : ℕ => Set.indicator (tail k) g x)
          Filter.atTop (𝓝 (0 : ℝ)) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
      have h_eventually_zero :
          (fun k : ℕ => Set.indicator (tail k) g x)
            =ᶠ[Filter.atTop] fun _ : ℕ => (0 : ℝ) := by
        refine Filter.eventually_atTop.2 ?_
        refine ⟨N, ?_⟩
        intro k hk
        have hk' : ¬ (k : ℝ) ≤ ‖x‖ := by
          have hx_lt : ‖x‖ < (k : ℝ) := lt_of_lt_of_le hN (Nat.cast_le.mpr hk)
          exact not_le_of_gt hx_lt
        simp [tail, hk', hg_def]
      exact
        (Filter.Tendsto.congr' h_eventually_zero.symm)
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0))
    have h_tendsto' :=
      MeasureTheory.tendsto_integral_of_dominated_convergence g h_meas
        hg_integrable h_bound h_lim
    simpa using h_tendsto'
  have h_eventually : ∀ᶠ k : ℕ in Filter.atTop,
      ∫ x in tail k, g x ∂volume < ε := by
    have h_tail_nonneg : ∀ k : ℕ, 0 ≤ ∫ x in tail k, g x ∂volume := by
      intro k
      have h_indicator_nonneg :
          0 ≤ᵐ[volume] fun x => Set.indicator (tail k) g x :=
        Filter.Eventually.of_forall (fun x => by
          by_cases hx : x ∈ tail k
          · simp [tail, hx, hg_def]
          · simp [tail, hx, hg_def])
      have h_eq : ∫ x, Set.indicator (tail k) g x ∂volume
          = ∫ x in tail k, g x ∂volume :=
        MeasureTheory.integral_indicator (h_tail_meas k)
      have h_integral_nonneg :
          0 ≤ ∫ x, Set.indicator (tail k) g x ∂volume :=
        MeasureTheory.integral_nonneg_of_ae h_indicator_nonneg
      simpa [h_eq]
        using h_integral_nonneg
    have h_dist := (Metric.tendsto_nhds.mp h_tendsto) ε (by simpa using hε)
    refine h_dist.mono ?_
    intro k hk
    have h_eq : ∫ x, Set.indicator (tail k) g x ∂volume
        = ∫ x in tail k, g x ∂volume :=
      MeasureTheory.integral_indicator (h_tail_meas k)
    simpa [Real.dist_eq, h_eq, abs_of_nonneg (h_tail_nonneg k)] using hk
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually
  let M : ℕ := max N 1
  have hM_ge_N : N ≤ M := le_max_left _ _
  have hM_ge_one : 1 ≤ M := le_max_right _ _
  have hM_pos_nat : 0 < M := lt_of_lt_of_le (Nat.succ_pos 0) hM_ge_one
  have hM_tail_lt : ∫ x in tail M, g x ∂volume < ε := hN M hM_ge_N
  have hM_pos : 0 < (M : ℝ) := by exact_mod_cast hM_pos_nat
  refine ⟨(M : ℝ), hM_pos, ?_⟩
  have h_eq :
      ∫ x, ‖f x‖ ∂(volume.restrict {x | (M : ℝ) ≤ ‖x‖})
        = ∫ x in tail M, g x ∂volume := by
    rfl
  simpa [tail, hg_def, h_eq]
    using hM_tail_lt
end Newton

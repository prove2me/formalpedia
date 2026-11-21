-- Prove2me | solution 1 for MasulloGRH.nuclear_convergence_exhaustive_projections
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:06:14.60017+00:00
-- url     : https://prove2.me/submissions/8d7217bb-41d6-4081-8daa-17c0925bc851

import Theorems.Thm_MasulloGRH_operatorTrace_of_nuclear_series
import Theorems.Thm_MasulloGRH_traceNorm_le_nuclear_series

-- Adapted from dga471’s public Prove2Me submission 21248ebf-b643-4e90-bf25-5d88a3888cd0.
open MasulloGRH Filter Topology Set
open scoped ComplexOrder

private theorem positive_traceNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) : 0 ≤ traceNorm T := by
  let b := chosenHilbertBasis H
  let d (i : (exists_hilbertBasis ℂ H).choose) := inner ℂ (b i) (operatorAbs T (b i))
  change 0 ≤ (∑' i, d i).re
  by_cases hs : Summable d
  · rw [Complex.re_tsum hs]
    have hp := (ContinuousLinearMap.nonneg_iff_isPositive (operatorAbs T)).mp
      (CFC.sqrt_nonneg _)
    exact tsum_nonneg fun i => hp.re_inner_nonneg_right (b i)
  · simp [tsum_eq_zero_of_not_summable hs]

private theorem vanishing_cost {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (R : ℕ → H →L[ℂ] H) (a b : ℕ → ℕ → H) (bound : ℕ → ℝ)
    (hs : Summable bound) (hle : ∀ i m, ‖a i m‖ * ‖b i m‖ ≤ bound m)
    (hlim : ∀ m, Tendsto (fun i => ‖a i m‖ * ‖b i m‖) atTop (𝓝 0))
    (hr : ∀ i u, HasSum (fun m => inner ℂ (a i m) u • b i m) (R i u)) :
    Tendsto (fun i => traceNorm (R i)) atTop (𝓝 0) := by
  have hc : Tendsto (fun i => ∑' m, ‖a i m‖ * ‖b i m‖) atTop (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence (g := fun _ => (0:ℝ)) hs hlim
      (Eventually.of_forall fun i m => by simpa [Real.norm_eq_abs, abs_of_nonneg] using hle i m)
  apply squeeze_zero (fun i => positive_traceNorm _) _ hc
  exact fun i => traceNorm_le_nuclear_series _ _ _
    (hs.of_nonneg_of_le (fun _ => by positivity) (hle i)) (hr i)

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (K : ℕ → Submodule ℂ H)
    [∀ i, (K i).HasOrthogonalProjection] (hK : Monotone K) (hcl : ∀ i, IsClosed (K i : Set H))
    (hdense : Dense (⋃ i, (K i : Set H))) (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    (∀ u : H, Tendsto (fun i => (K i).starProjection u) atTop (𝓝 u)) ∧
    Tendsto (fun i => traceNorm ((K i).starProjection ∘L T - T)) atTop (𝓝 0) ∧
    Tendsto (fun i => traceNorm (T ∘L (K i).starProjection - T)) atTop (𝓝 0) ∧
    Tendsto (fun i => operatorTrace ((K i).starProjection ∘L T)) atTop (𝓝 (operatorTrace T)) ∧
    Tendsto (fun i => operatorTrace (T ∘L (K i).starProjection)) atTop (𝓝 (operatorTrace T)) := by
  let P (i : ℕ) := (K i).starProjection
  have hstrong (u : H) : Tendsto (fun i => P i u) atTop (𝓝 u) := by
    apply Submodule.starProjection_tendsto_self K hK
    intro x _
    exact closure_mono (iUnion_subset fun i => (le_iSup K i : K i ≤ ⨆ j, K j)) (hdense x)
  obtain ⟨x, y, hs, hxy⟩ := hT
  have hdiff (i : ℕ) (z : H) : ‖P i z - z‖ ≤ 2 * ‖z‖ := by
    linarith [norm_sub_le (P i z) z, (K i).norm_starProjection_apply_le z]
  have hzero (z : H) : Tendsto (fun i => ‖P i z - z‖) atTop (𝓝 0) := by
    simpa using ((hstrong z).sub (tendsto_const_nhds (x := z))).norm
  have hl (i : ℕ) (u : H) := (hxy u).mapL (P i)
  have hr (i : ℕ) (u : H) := hxy (P i u)
  have hright (i : ℕ) (u : H) : HasSum (fun m => inner ℂ (P i (x m)) u • y m) (T (P i u)) := by
    simpa only [P, Submodule.inner_starProjection_left_eq_right] using hr i u
  refine ⟨hstrong, ?_, ?_, ?_, ?_⟩
  · apply vanishing_cost _ (fun _ => x) (fun i m => P i (y m) - y m)
      (fun m => 2 * (‖x m‖ * ‖y m‖)) (hs.mul_left 2)
    · intro i m
      nlinarith [mul_le_mul_of_nonneg_left (hdiff i (y m)) (norm_nonneg (x m))]
    · intro m
      simpa using (hzero (y m)).const_mul ‖x m‖
    · intro i u
      simpa only [map_smul, smul_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
        using (hl i u).sub (hxy u)
  · apply vanishing_cost _ (fun i m => P i (x m) - x m) (fun _ => y)
      (fun m => 2 * (‖x m‖ * ‖y m‖)) (hs.mul_left 2)
    · intro i m
      nlinarith [mul_le_mul_of_nonneg_right (hdiff i (x m)) (norm_nonneg (y m))]
    · intro m
      simpa using (hzero (x m)).mul_const ‖y m‖
    · intro i u
      simpa only [inner_sub_left, sub_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
        using (hright i u).sub (hxy u)
  · rw [operatorTrace_of_nuclear_series T x y hs hxy]
    have he i := operatorTrace_of_nuclear_series (P i ∘L T) x (fun m => P i (y m))
      (hs.of_nonneg_of_le (fun _ => by positivity) (fun m => mul_le_mul_of_nonneg_left
        ((K i).norm_starProjection_apply_le _) (norm_nonneg _))) (fun u => by simpa using hl i u)
    change Tendsto (fun i => operatorTrace (P i ∘L T)) _ _
    simp_rw [he]
    apply tendsto_tsum_of_dominated_convergence hs
    · intro m
      exact tendsto_const_nhds.inner (hstrong (y m))
    · exact Eventually.of_forall fun i m => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left ((K i).norm_starProjection_apply_le _) (norm_nonneg _))
  · rw [operatorTrace_of_nuclear_series T x y hs hxy]
    have he i := operatorTrace_of_nuclear_series (T ∘L P i) (fun m => P i (x m)) y
      (hs.of_nonneg_of_le (fun _ => by positivity) (fun m => mul_le_mul_of_nonneg_right
        ((K i).norm_starProjection_apply_le _) (norm_nonneg _))) (hright i)
    change Tendsto (fun i => operatorTrace (T ∘L P i)) _ _
    simp_rw [he]
    apply tendsto_tsum_of_dominated_convergence hs
    · intro m
      exact (hstrong (x m)).inner tendsto_const_nhds
    · exact Eventually.of_forall fun i m => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right ((K i).norm_starProjection_apply_le _) (norm_nonneg _))

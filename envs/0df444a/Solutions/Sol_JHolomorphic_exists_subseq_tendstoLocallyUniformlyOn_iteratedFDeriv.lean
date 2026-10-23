-- Prove2me | solution 1 for JHolomorphic.exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T15:35:47.209331+00:00
-- url     : https://prove2.me/submissions/8a879aa8-de2b-4c0b-922b-16220ac8a458

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Topology.Sequences



namespace JHolomorphic

open Metric Filter Topology Set
open scoped ContDiff

theorem exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv_aux
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {U : Set X} (hU : IsOpen U) (f : ℕ → X → Y) (hf : ∀ ν, ContDiffOn ℝ ∞ (f ν) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∀ m : ℕ, ∃ M : ℝ, ∀ ν, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (f ν) x‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : (m : ℕ) → X → ContinuousMultilinearMap ℝ (fun _ : Fin m => X) Y,
        ∀ m, TendstoLocallyUniformlyOn (fun ν => iteratedFDeriv ℝ m (f (φ ν))) (g m) atTop U := by
  have hprop : ∀ m : ℕ, ProperSpace (ContinuousMultilinearMap ℝ (fun _ : Fin m => X) Y) := by
    intro m
    haveI : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin m => X) Y) :=
      FiniteDimensional.of_injective
        (ContinuousMultilinearMap.toMultilinearMapLinear (A := ℝ) (R' := ℝ)
          (M₁ := fun _ : Fin m => X) (M₂ := Y))
        ContinuousMultilinearMap.toMultilinearMap_injective
    exact FiniteDimensional.proper_real _
  -- local uniform Lipschitz bounds for every derivative
  have hlip : ∀ m : ℕ, ∀ x ∈ U, ∃ r > 0, ∃ B ≥ (0 : ℝ), ball x r ⊆ U ∧
      ∀ ν, ∀ y ∈ ball x r, ∀ y' ∈ ball x r,
        ‖iteratedFDeriv ℝ m (f ν) y - iteratedFDeriv ℝ m (f ν) y'‖ ≤ B * ‖y - y'‖ := by
    intro m x hx
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
    have hKU : closedBall x (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
    obtain ⟨M, hM⟩ := hb _ hKU (isCompact_closedBall x _) (m + 1)
    refine ⟨ε / 2, by linarith, max M 0, le_max_right _ _, ball_subset_closedBall.trans hKU, ?_⟩
    intro ν y hy y' hy'
    have hdiff : ∀ z ∈ ball x (ε / 2), DifferentiableAt ℝ (iteratedFDeriv ℝ m (f ν)) z := by
      intro z hz
      exact ((hf ν).contDiffAt (hU.mem_nhds (ball_subset_closedBall.trans hKU hz))).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.coe_lt_top m)
    have hbd : ∀ z ∈ ball x (ε / 2), ‖fderiv ℝ (iteratedFDeriv ℝ m (f ν)) z‖ ≤ max M 0 := by
      intro z hz
      rw [norm_fderiv_iteratedFDeriv]
      exact (hM ν z (ball_subset_closedBall hz)).trans (le_max_left _ _)
    exact (convex_ball x (ε / 2)).norm_image_sub_le_of_norm_fderiv_le hdiff hbd hy' hy
  have hsmall : ∀ B ≥ (0 : ℝ), ∀ ε > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < ε / (4 * (B + 1)) →
      B * t ≤ ε / 4 := by
    intro B hB ε hε t ht0 ht
    have h1 : B * t ≤ (B + 1) * t := by nlinarith
    have h2 : (B + 1) * t ≤ (B + 1) * (ε / (4 * (B + 1))) :=
      mul_le_mul_of_nonneg_left ht.le (by linarith)
    have h3 : (B + 1) * (ε / (4 * (B + 1))) = ε / 4 := by field_simp
    linarith
  -- extraction on a countable dense subset of `U`
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense X
  haveI : Countable (U ∩ S : Set X) := (hSc.mono inter_subset_right).to_subtype
  have hbpt : ∀ p : ℕ × (U ∩ S : Set X), ∃ M : ℝ, ∀ ν,
      ‖iteratedFDeriv ℝ p.1 (f ν) p.2‖ ≤ M := by
    intro p
    obtain ⟨M, hM⟩ := hb {(p.2 : X)} (singleton_subset_iff.2 p.2.2.1) isCompact_singleton p.1
    exact ⟨M, fun ν => hM ν _ rfl⟩
  choose Bd hBd using hbpt
  let A : ℕ → ((p : ℕ × (U ∩ S : Set X)) → ContinuousMultilinearMap ℝ (fun _ : Fin p.1 => X) Y) :=
    fun ν p => iteratedFDeriv ℝ p.1 (f ν) p.2
  have hQ : IsCompact (Set.pi univ fun p : ℕ × (U ∩ S : Set X) =>
      closedBall (0 : ContinuousMultilinearMap ℝ (fun _ : Fin p.1 => X) Y) (Bd p)) :=
    isCompact_univ_pi fun p => by
      haveI := hprop p.1
      exact isCompact_closedBall _ _
  have hA : ∀ ν, A ν ∈ Set.pi univ fun p : ℕ × (U ∩ S : Set X) =>
      closedBall (0 : ContinuousMultilinearMap ℝ (fun _ : Fin p.1 => X) Y) (Bd p) := by
    intro ν p _
    simpa [A] using hBd p ν
  obtain ⟨a, -, φ, hφ, hlim⟩ := hQ.tendsto_subseq hA
  rw [tendsto_pi_nhds] at hlim
  -- pointwise Cauchy property on all of `U`
  have hcau : ∀ m : ℕ, ∀ x ∈ U, CauchySeq (fun ν => iteratedFDeriv ℝ m (f (φ ν)) x) := by
    intro m x hx
    obtain ⟨r, hr, B, hB0, -, hB⟩ := hlip m x hx
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hxcl : x ∈ closure (U ∩ S) := hSd.open_subset_closure_inter hU hx
    obtain ⟨s, hsT, hxs⟩ := Metric.mem_closure_iff.1 hxcl (min r (ε / (4 * (B + 1))))
      (lt_min hr (by positivity))
    have hs_ball : s ∈ ball x r := by
      rw [mem_ball, dist_comm]; exact hxs.trans_le (min_le_left _ _)
    have hconv : Tendsto (fun ν => iteratedFDeriv ℝ m (f (φ ν)) s) atTop (𝓝 (a (m, ⟨s, hsT⟩))) :=
      hlim (m, ⟨s, hsT⟩)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hconv.cauchySeq (ε / 2) (by linarith)
    refine ⟨N, fun n hn => ?_⟩
    have hxs' : ‖x - s‖ < ε / (4 * (B + 1)) := by
      rw [← dist_eq_norm]; exact hxs.trans_le (min_le_right _ _)
    have hBx := hsmall B hB0 ε hε _ (norm_nonneg _) hxs'
    have h1 := hB (φ n) x (mem_ball_self hr) s hs_ball
    have h2 := hB (φ N) s hs_ball x (mem_ball_self hr)
    rw [norm_sub_rev s x] at h2
    have h3 := hN n hn
    calc dist (iteratedFDeriv ℝ m (f (φ n)) x) (iteratedFDeriv ℝ m (f (φ N)) x)
        ≤ dist (iteratedFDeriv ℝ m (f (φ n)) x) (iteratedFDeriv ℝ m (f (φ n)) s)
          + dist (iteratedFDeriv ℝ m (f (φ n)) s) (iteratedFDeriv ℝ m (f (φ N)) s)
          + dist (iteratedFDeriv ℝ m (f (φ N)) s) (iteratedFDeriv ℝ m (f (φ N)) x) :=
          dist_triangle4 _ _ _ _
      _ < ε := by rw [dist_eq_norm, dist_eq_norm (iteratedFDeriv ℝ m (f (φ N)) s)]; linarith
  let g : (m : ℕ) → X → ContinuousMultilinearMap ℝ (fun _ : Fin m => X) Y :=
    fun m x => limUnder atTop (fun ν => iteratedFDeriv ℝ m (f (φ ν)) x)
  have hgt : ∀ m : ℕ, ∀ x ∈ U,
      Tendsto (fun ν => iteratedFDeriv ℝ m (f (φ ν)) x) atTop (𝓝 (g m x)) :=
    fun m x hx => tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcau m x hx))
  refine ⟨φ, hφ, g, fun m => ?_⟩
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  obtain ⟨r, hr, B, hB0, hrU, hB⟩ := hlip m x hx
  have hδ : 0 < min r (ε / (4 * (B + 1))) := lt_min hr (by positivity)
  refine ⟨ball x (min r (ε / (4 * (B + 1)))), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hδ), ?_⟩
  filter_upwards [Metric.tendsto_nhds.1 (hgt m x hx) (ε / 2) (by linarith)] with n hn y hy
  have hyr : y ∈ ball x r := ball_subset_ball (min_le_left _ _) hy
  have hyx : ‖y - x‖ < ε / (4 * (B + 1)) := by
    rw [← dist_eq_norm]; exact (mem_ball.1 hy).trans_le (min_le_right _ _)
  have hBy := hsmall B hB0 ε hε _ (norm_nonneg _) hyx
  have hgy : dist (g m y) (g m x) ≤ B * ‖y - x‖ := by
    refine le_of_tendsto ((hgt m y (hrU hyr)).dist (hgt m x hx)) (Eventually.of_forall fun k => ?_)
    rw [dist_eq_norm]; exact hB _ y hyr x (mem_ball_self hr)
  have hFn : dist (iteratedFDeriv ℝ m (f (φ n)) x) (iteratedFDeriv ℝ m (f (φ n)) y)
      ≤ B * ‖y - x‖ := by
    rw [dist_eq_norm, norm_sub_rev y x]; exact hB _ x (mem_ball_self hr) y hyr
  rw [dist_comm] at hn
  calc dist (g m y) (iteratedFDeriv ℝ m (f (φ n)) y)
      ≤ dist (g m y) (g m x) + dist (g m x) (iteratedFDeriv ℝ m (f (φ n)) x)
        + dist (iteratedFDeriv ℝ m (f (φ n)) x) (iteratedFDeriv ℝ m (f (φ n)) y) :=
        dist_triangle4 _ _ _ _
    _ < ε := by linarith

end JHolomorphic

open JHolomorphic

open Metric Filter Topology Set
open scoped ContDiff

theorem solution
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {U : Set X} (hU : IsOpen U) (f : ℕ → X → Y) (hf : ∀ ν, ContDiffOn ℝ ∞ (f ν) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∀ m : ℕ, ∃ M : ℝ, ∀ ν, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (f ν) x‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : (m : ℕ) → X → ContinuousMultilinearMap ℝ (fun _ : Fin m => X) Y,
        ∀ m, TendstoLocallyUniformlyOn (fun ν => iteratedFDeriv ℝ m (f (φ ν))) (g m) atTop U :=
  exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv_aux hU f hf hb

-- Prove2me | solution 1 for NoHair.regular_static_vacuum_positive_end_zero_mass
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T07:41:52.389622+00:00
-- url     : https://prove2.me/submissions/c4c021eb-6e1f-462b-a588-58623aa92375
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_static_conformal_adm_flux_law
import Theorems.Thm_NoHair_regular_static_vacuum_adm_lapse_flux
open Set Filter NoHair
open scoped Topology ContDiff Manifold

private lemma decay {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) : HasStaticFirstOrderFalloff c.N c.h := by
  obtain ⟨R₀,C₀,p₀,a₀,h₀⟩ := c.falloff 0
  obtain ⟨R₁,C₁,p₁,a₁,h₁⟩ := c.falloff 1
  obtain ⟨B,hB⟩ := c.compactComplement.isBounded.subset_closedBall (0:ADMPoint)
  let C := max C₀ C₁
  refine ⟨max R₀ (max R₁ B),C,p₀.trans_le (le_max_left _ _),a₀.trans_le (le_max_left _ _),?_⟩
  intro x hx
  have gx := max_lt_iff.mp hx
  have gy := max_lt_iff.mp gx.2
  have pos : 0 < ‖x‖ := p₀.trans gx.1
  have inΩ : x ∈ c.Ω := by
    by_contra h
    have d := Metric.mem_closedBall.mp (hB h)
    rw [dist_zero_right] at d
    exact gy.2.not_ge d
  have inW := c.extendsAcross (subset_closure inΩ)
  have hn := c.openExtension.mem_nhds inW
  have z := h₀ x gx.1
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,Nat.zero_add,pow_one] at z
  have o := h₁ x gy.1
  simp only [norm_iteratedFDeriv_one,fderiv_sub_const] at o
  have zer {a : ℝ} (h : a ≤ C₀/‖x‖) : a ≤ C/‖x‖ :=
    h.trans (div_le_div_of_nonneg_right (le_max_left _ _) pos.le)
  have derivBound (f : ADMPoint → ℝ) (i : Fin 3) (hf : ‖fderiv ℝ f x‖ ≤ C₁/‖x‖^2) :
      |‖x‖^2*spatialADMPartial i f x| ≤ C := by
    have e : ‖EuclideanSpace.single i (1:ℝ)‖ = 1 := by simp
    have b := (fderiv ℝ f x).le_opNorm (EuclideanSpace.single i (1:ℝ))
    rw [e,mul_one,Real.norm_eq_abs] at b
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    calc ‖x‖^2*|spatialADMPartial i f x| ≤ ‖x‖^2*(C₁/‖x‖^2) := mul_le_mul_of_nonneg_left (b.trans hf) (sq_nonneg _)
         _ = C₁ := by field_simp [pos.ne']
         _ ≤ C := le_max_right _ _
  exact ⟨(c.smoothLapse.contDiffAt hn).of_le (by simp),
    fun i j => ((c.smoothMetric i j).contDiffAt hn).of_le (by simp),zer z.1,
    fun i j => zer (z.2 i j),fun i => derivBound c.N i o.1,
    fun i j k => derivBound _ k (o.2 i j)⟩

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) :
    Tendsto (staticADMFlux (staticPositiveMetric c.N c.h)) atTop (𝓝 0) := by
  have a := static_conformal_adm_flux_law c.N c.h (decay g φ D c)
  have b := regular_static_vacuum_adm_lapse_flux g φ D c
  have h := a.add b
  have hn : Tendsto (fun r => (staticADMFlux (staticPositiveMetric c.N c.h) r -
      staticADMFlux c.h r + staticLapseFlux c.N r) +
      (staticADMFlux c.h r - staticLapseFlux c.N r)) atTop (𝓝 0) := by
    simpa only [add_zero] using h
  apply hn.congr'
  filter_upwards with r
  ring


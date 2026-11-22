-- Prove2me | solution 1 for LocallyConvexDuality.nhds_zero_hasBasis_polar_equicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:10:59.51344+00:00
-- url     : https://prove2.me/submissions/652ed36a-dd9f-4a05-a2e1-15aee50aa1fa

import Mathlib

open scoped Topology ComplexOrder

set_option autoImplicit false

namespace Sol_LocallyConvexDuality_nhds_zero_hasBasis_polar_equicontinuous

/-- Hahn–Banach for a continuous seminorm: every point is normed by a continuous linear functional
dominated by the seminorm. -/
theorem exists_strongDual_eq_seminorm {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [PolynormableSpace 𝕜 E]
    (q : Seminorm 𝕜 E) (hq : Continuous q) (x : E) :
    ∃ g : StrongDual 𝕜 E, ‖g x‖ = q x ∧ ∀ y, ‖g y‖ ≤ q y := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx], fun y => by simp⟩
  · -- the functional `a • x ↦ a * q x` on the line spanned by `x`
    let f : Module.Dual 𝕜 (Submodule.span 𝕜 ({x} : Set E)) :=
      ((q x : ℝ) : 𝕜) • (LinearEquiv.coord 𝕜 E x hx).toLinearMap
    have hf : ∀ y : Submodule.span 𝕜 ({x} : Set E), ‖f y‖ = q (y : E) := by
      intro y
      have hy : (LinearEquiv.coord 𝕜 E x hx y) • x = (y : E) :=
        LinearEquiv.coord_apply_smul 𝕜 E x hx y
      have h1 : f y = ((q x : ℝ) : 𝕜) * LinearEquiv.coord 𝕜 E x hx y := rfl
      rw [h1, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg q x), ← hy,
        map_smul_eq_mul, mul_comm]
    obtain ⟨g, hg, hgq⟩ :=
      Module.Dual.exists_continuous_extension_of_le_seminorm
        (Submodule.span 𝕜 ({x} : Set E)) f hq (fun y => (hf y).le)
    refine ⟨g, ?_, hgq⟩
    have hxmem : x ∈ Submodule.span 𝕜 ({x} : Set E) := Submodule.mem_span_singleton_self x
    have h2 := hg ⟨x, hxmem⟩
    have h3 := hf ⟨x, hxmem⟩
    simp only at h2 h3
    rw [h2, h3]

end Sol_LocallyConvexDuality_nhds_zero_hasBasis_polar_equicontinuous

theorem solution {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E] :
    (𝓝 (0 : E)).HasBasis
      (fun A : Set (WeakDual 𝕜 E) =>
        Equicontinuous (fun f : A => ((f : WeakDual 𝕜 E) : E → 𝕜)) ∧ AbsConvex 𝕜 A ∧ IsClosed A)
      (fun A : Set (WeakDual 𝕜 E) => {x : E | ∀ f ∈ A, ‖f x‖ ≤ 1}) := by
  refine ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩
  · -- a neighbourhood of `0` contains a ball of a continuous seminorm `q`
    obtain ⟨⟨s, r⟩, hr, hsub⟩ :=
      (PolynormableSpace.withSeminorms 𝕜 E).hasBasis_zero_ball.mem_iff.mp ht
    simp only at hr hsub
    set q : Seminorm 𝕜 E := s.sup (fun p : {p : Seminorm 𝕜 E // Continuous p} => p.1) with hqdef
    have hq : Continuous q := Seminorm.continuous_finsetSup fun i _ => i.2
    -- `A` is the set of functionals dominated by `(2 / r) • q`
    have hc : 0 < 2 / r := by positivity
    refine ⟨{f : WeakDual 𝕜 E | ∀ x, ‖f x‖ ≤ 2 / r * q x}, ⟨?_, ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · -- equicontinuity
      intro x₀ U hU
      obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
      have hcont : Continuous fun x : E => 2 / r * q (x₀ - x) :=
        continuous_const.mul (hq.comp (continuous_const.sub continuous_id))
      have htend : Filter.Tendsto (fun x : E => 2 / r * q (x₀ - x)) (𝓝 x₀) (𝓝 0) :=
        hcont.tendsto' x₀ 0 (by simp)
      filter_upwards [htend.eventually (eventually_lt_nhds hε)] with x hx
      rintro ⟨f, hf⟩
      apply hεU
      have h1 : dist (f x₀) (f x) = ‖f (x₀ - x)‖ := by
        rw [dist_eq_norm, map_sub]
      show dist (f x₀) (f x) < ε
      rw [h1]
      exact (hf (x₀ - x)).trans_lt hx
    · -- balanced
      rw [balanced_iff_smul_mem]
      intro a ha f hf x
      have h1 : (a • f) x = a * f x := rfl
      rw [h1, norm_mul]
      calc ‖a‖ * ‖f x‖ ≤ 1 * (2 / r * q x) :=
            mul_le_mul ha (hf x) (norm_nonneg _) zero_le_one
        _ = 2 / r * q x := one_mul _
    · -- convex
      intro f hf g hg a b ha hb hab x
      have h1 : (a • f + b • g) x = a * f x + b * g x := rfl
      have hna : ‖a‖ = RCLike.re a := by
        have h := congrArg RCLike.re (RCLike.norm_of_nonneg' ha)
        simpa using h
      have hnb : ‖b‖ = RCLike.re b := by
        have h := congrArg RCLike.re (RCLike.norm_of_nonneg' hb)
        simpa using h
      have hsum : ‖a‖ + ‖b‖ = 1 := by
        rw [hna, hnb, ← map_add, hab, RCLike.one_re]
      rw [h1]
      calc ‖a * f x + b * g x‖ ≤ ‖a * f x‖ + ‖b * g x‖ := norm_add_le _ _
        _ = ‖a‖ * ‖f x‖ + ‖b‖ * ‖g x‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖a‖ * (2 / r * q x) + ‖b‖ * (2 / r * q x) :=
            add_le_add (mul_le_mul_of_nonneg_left (hf x) (norm_nonneg _))
              (mul_le_mul_of_nonneg_left (hg x) (norm_nonneg _))
        _ = 2 / r * q x := by rw [← add_mul, hsum, one_mul]
    · -- weak-* closed
      have hInter : {f : WeakDual 𝕜 E | ∀ x, ‖f x‖ ≤ 2 / r * q x} =
          ⋂ x : E, {f : WeakDual 𝕜 E | ‖f x‖ ≤ 2 / r * q x} := by
        ext f
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [hInter]
      exact isClosed_iInter fun x =>
        isClosed_le (continuous_norm.comp (WeakDual.eval_continuous x)) continuous_const
    · -- the polar of `A` is contained in the ball of `q`, by Hahn–Banach
      intro x hx
      apply hsub
      obtain ⟨g, hgx, hgq⟩ :=
        Sol_LocallyConvexDuality_nhds_zero_hasBasis_polar_equicontinuous.exists_strongDual_eq_seminorm
          q hq x
      have hmem : ((2 / r : ℝ) : 𝕜) • (StrongDual.toWeakDual g) ∈
          {f : WeakDual 𝕜 E | ∀ x, ‖f x‖ ≤ 2 / r * q x} := by
        intro y
        have h1 : (((2 / r : ℝ) : 𝕜) • (StrongDual.toWeakDual g)) y =
            ((2 / r : ℝ) : 𝕜) * g y := rfl
        rw [h1, norm_mul, RCLike.norm_ofReal, abs_of_pos hc]
        exact mul_le_mul_of_nonneg_left (hgq y) hc.le
      have h2 := hx _ hmem
      have h1 : (((2 / r : ℝ) : 𝕜) • (StrongDual.toWeakDual g)) x =
          ((2 / r : ℝ) : 𝕜) * g x := rfl
      rw [h1, norm_mul, RCLike.norm_ofReal, abs_of_pos hc, hgx] at h2
      rw [Seminorm.mem_ball_zero]
      have h3 : q x ≤ r / 2 := by
        have h4 : 2 / r * q x = q x / (r / 2) := by field_simp
        rw [h4, div_le_one (by positivity)] at h2
        exact h2
      linarith
  · -- the polar of an equicontinuous set is a neighbourhood of `0`
    rintro ⟨A, ⟨hA, -, -⟩, hAt⟩
    refine Filter.mem_of_superset ?_ hAt
    have h := hA 0 _ (Metric.dist_mem_uniformity (α := 𝕜) one_pos)
    filter_upwards [h] with x hx f hf
    have h1 := hx ⟨f, hf⟩
    simp only [map_zero, dist_zero_left] at h1
    exact h1.le

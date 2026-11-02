-- Prove2me | solution 1 for HryniewiczCriterion.exists_fderiv_page_eq_hamiltonianVectorField
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T16:15:55.585904+00:00
-- url     : https://prove2.me/submissions/deaaf01e-f41f-4c2f-a1c4-19fd9b14acb0

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace

open HryniewiczCriterion
open scoped ContDiff
open scoped ContDiff Topology
open Filter

namespace HryniewiczCriterion

lemma rb1_isClosed_closedUnitDisk : IsClosed closedUnitDisk :=
  isClosed_le (by fun_prop) continuous_const

lemma rb1_isOpen_openUnitDisk : IsOpen openUnitDisk :=
  isOpen_lt (by fun_prop) continuous_const

lemma rb1_isCompact_closedUnitDisk : IsCompact closedUnitDisk := by
  refine Metric.isCompact_of_isClosed_isBounded rb1_isClosed_closedUnitDisk ?_
  refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := 1)).subset ?_
  intro u hu
  have hu' : u 0 ^ 2 + u 1 ^ 2 ≤ 1 := hu
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_le]
  fin_cases i <;> simp <;> constructor <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]

lemma rb1_openUnitDisk_subset : openUnitDisk ⊆ closedUnitDisk := fun u hu =>
  le_of_lt (show u 0 ^ 2 + u 1 ^ 2 < 1 from hu)

/-- Every unit vector is `(cos 2πt, sin 2πt)`. -/
lemma rb1_cos_sin (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ t : ℝ, Real.cos (2 * Real.pi * t) = a ∧ Real.sin (2 * Real.pi * t) = b := by
  set z : ℂ := ⟨a, b⟩
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [z, ← sq, h]
  have hz : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  refine ⟨Complex.arg z / (2 * Real.pi), ?_, ?_⟩
  · rw [mul_div_cancel₀ _ (by positivity), Complex.cos_arg hz, hn, div_one]
  · rw [mul_div_cancel₀ _ (by positivity), Complex.sin_arg, hn, div_one]

/-- A point of the closed disk off the open disk is a circle point. -/
lemma rb1_exists_circlePoint {v : Plane} (hv : v ∈ closedUnitDisk) (hv' : v ∉ openUnitDisk) :
    ∃ t, v = circlePoint t := by
  have h1 : v 0 ^ 2 + v 1 ^ 2 ≤ 1 := hv
  have h2 : ¬ v 0 ^ 2 + v 1 ^ 2 < 1 := hv'
  obtain ⟨t, ht1, ht2⟩ := rb1_cos_sin (v 0) (v 1) (by linarith [not_lt.1 h2])
  refine ⟨t, ?_⟩
  ext j; fin_cases j
  · simp [circlePoint, ht1]
  · simp [circlePoint, ht2]

/-- `dH(x)(X_H(x)) = 0`. -/
lemma rb1_dH_hvf (H : R4 → ℝ) (x : R4) :
    fderiv ℝ H x (hamiltonianVectorField H x) = 0 := by
  set X := hamiltonianVectorField H x
  have hX : X = ∑ i : Fin 4, X i • (Pi.single i (1 : ℝ) : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [hX, map_sum]
  simp only [map_smul, smul_eq_mul, Fin.sum_univ_four]
  simp [X, hamiltonianVectorField, partialDeriv]
  ring

lemma rb1_continuous_hvf {H : R4 → ℝ} (hH : ContDiff ℝ ∞ H) :
    Continuous (hamiltonianVectorField H) := by
  have hc : Continuous (fderiv ℝ H) := hH.continuous_fderiv (by simp)
  have hp : ∀ i, Continuous fun x => partialDeriv H x i := fun i =>
    hc.clm_apply continuous_const
  refine continuous_pi fun j => ?_
  fin_cases j
  · exact (hp 1).neg
  · exact hp 0
  · exact (hp 3).neg
  · exact hp 2

end HryniewiczCriterion

namespace HryniewiczCriterion

/-- On an open-disk page point, `X_H` is the image of a tangent vector of the joint page
map whose parameter component is nonzero. -/
lemma rb1_exists_preimage_hvf (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (page : ℝ → Plane → R4) (hsm : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2))
    (hpS : ∀ θ, page θ '' closedUnitDisk ⊆ energySurface H)
    (htr : ∀ θ, ∀ u ∈ openUnitDisk,
      hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u))
    (hreg : ∀ θ : ℝ, ∀ u ∈ openUnitDisk,
      Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u)))
    {θ₀ : ℝ} {v₀ : Plane} (hv₀ : v₀ ∈ openUnitDisk) :
    ∃ w : ℝ × Plane, fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ₀, v₀) w =
      hamiltonianVectorField H (page θ₀ v₀) ∧ w.1 ≠ 0 := by
  set e : ℝ × Plane → R4 := fun z => page z.1 z.2 with he_def
  set p : ℝ × Plane := (θ₀, v₀)
  set De := fderiv ℝ e p
  set x := page θ₀ v₀
  have hxe : e p = x := rfl
  have hHd : DifferentiableAt ℝ H x := (hS.1.differentiable (by simp)) x
  have hed : DifferentiableAt ℝ e p := (hsm.differentiable (by simp)) p
  -- `H ∘ e ≡ 1` near `p`
  have hloc : (H ∘ e) =ᶠ[𝓝 p] fun _ => (1 : ℝ) := by
    have : ∀ᶠ z in 𝓝 p, z.2 ∈ openUnitDisk :=
      (continuous_snd.isOpen_preimage _ rb1_isOpen_openUnitDisk).mem_nhds hv₀
    filter_upwards [this] with z hz
    exact hpS z.1 ⟨z.2, rb1_openUnitDisk_subset hz, rfl⟩
  have hcomp : (fderiv ℝ H x).comp De = 0 := by
    have h1 : HasFDerivAt (H ∘ e) ((fderiv ℝ H x).comp De) p := by
      exact hHd.hasFDerivAt.comp p hed.hasFDerivAt
    have h2 : HasFDerivAt (H ∘ e) (0 : ℝ × Plane →L[ℝ] ℝ) p :=
      (hasFDerivAt_const (1 : ℝ) p).congr_of_eventuallyEq hloc
    exact h1.unique h2
  -- range `De` = ker `dH`
  have hle : LinearMap.range (De : ℝ × Plane →ₗ[ℝ] R4) ≤
      LinearMap.ker (fderiv ℝ H x : R4 →ₗ[ℝ] ℝ) := by
    rintro _ ⟨w, rfl⟩
    have := congrArg (fun L : ℝ × Plane →L[ℝ] ℝ => L w) hcomp
    simpa using this
  have hxS : H x = 1 := hpS θ₀ ⟨v₀, rb1_openUnitDisk_subset hv₀, rfl⟩
  have hdx : 0 < fderiv ℝ H x x := hS.2.2 x hxS
  have hrng : LinearMap.range (fderiv ℝ H x : R4 →ₗ[ℝ] ℝ) = ⊤ := by
    rw [eq_top_iff]
    rintro c -
    refine ⟨(c / fderiv ℝ H x x) • x, ?_⟩
    simp [map_smul, div_mul_cancel₀ c hdx.ne']
  have hker : Module.finrank ℝ (LinearMap.ker (fderiv ℝ H x : R4 →ₗ[ℝ] ℝ)) = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ H x : R4 →ₗ[ℝ] ℝ)
    rw [hrng, finrank_top] at this
    simp at this
    omega
  have hran : Module.finrank ℝ (LinearMap.range (De : ℝ × Plane →ₗ[ℝ] R4)) = 3 := by
    rw [LinearMap.finrank_range_of_inj (hreg θ₀ v₀ hv₀)]
    simp
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hran, hker])
  have hXk : hamiltonianVectorField H x ∈ LinearMap.ker (fderiv ℝ H x : R4 →ₗ[ℝ] ℝ) :=
    rb1_dH_hvf H x
  rw [← heq] at hXk
  obtain ⟨w, hw⟩ := hXk
  refine ⟨w, hw, fun h0 => htr θ₀ v₀ hv₀ ⟨w.2, ?_⟩⟩
  -- `De (0, w.2) = d(page θ₀)(v₀) w.2`
  have hpd : HasFDerivAt (page θ₀) (De.comp (ContinuousLinearMap.inr ℝ ℝ Plane)) v₀ := by
    have hi : HasFDerivAt (fun v : Plane => ((θ₀, v) : ℝ × Plane))
        (ContinuousLinearMap.inr ℝ ℝ Plane) v₀ := hasFDerivAt_prodMk_right θ₀ v₀
    exact hed.hasFDerivAt.comp v₀ hi
  rw [hpd.fderiv]
  have hw' : w = (0, w.2) := Prod.ext h0 rfl
  rw [← hw]
  conv_rhs => rw [hw']
  rfl

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H)
    (page : ℝ → Plane → R4) (hsm : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2))
    (hpS : ∀ θ, page θ '' closedUnitDisk ⊆ energySurface H)
    (htr : ∀ θ, ∀ u ∈ openUnitDisk,
      hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u))
    (hreg : ∀ θ : ℝ, ∀ u ∈ openUnitDisk,
      Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u)))
    {θ₀ : ℝ} {v₀ : Plane} (hv₀ : v₀ ∈ openUnitDisk) :
    ∃ w : ℝ × Plane, fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ₀, v₀) w =
      hamiltonianVectorField H (page θ₀ v₀) ∧ w.1 ≠ 0 :=
  rb1_exists_preimage_hvf H hS page hsm hpS htr hreg hv₀

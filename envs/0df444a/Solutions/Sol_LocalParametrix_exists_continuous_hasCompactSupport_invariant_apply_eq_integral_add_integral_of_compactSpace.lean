-- Prove2me | solution 1 for LocalParametrix.exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b9fd654d-d648-55d1-9258-6230bf475faf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalParametrix_exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Topology Filter Set

namespace R4KAvg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (ρ : G →* (E →L[ℝ] E))

theorem rho_inv_apply (k : G) (x : E) : ρ k⁻¹ (ρ k x) = x := by
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]

theorem rho_apply_inv (k : G) (x : E) : ρ k (ρ k⁻¹ x) = x := by
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]

def rhoEquiv (k : G) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse (ρ k) (ρ k⁻¹) (rho_inv_apply ρ k) (rho_apply_inv ρ k)

@[scoped simp] theorem rhoEquiv_apply (k : G) (x : E) : rhoEquiv ρ k x = ρ k x := rfl

theorem det_rho_ne_zero (k : G) : LinearMap.det (ρ k : E →ₗ[ℝ] E) ≠ 0 := by
  have h : LinearMap.det (ρ k : E →ₗ[ℝ] E) * LinearMap.det (ρ k⁻¹ : E →ₗ[ℝ] E) = 1 := by
    rw [← LinearMap.det_comp, ← ContinuousLinearMap.toLinearMap_comp, ← ContinuousLinearMap.mul_def, ← map_mul,
      mul_inv_cancel, map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id, LinearMap.det_id]
  exact left_ne_zero_of_mul_eq_one h

theorem exists_stable_nhds (hρ : Continuous fun p : G × E => ρ p.1 p.2) (x₀ : E) (hx₀ : ∀ k : G, ρ k x₀ = x₀)
    {V : Set E} (hV : V ∈ 𝓝 x₀) :
    ∃ W ∈ 𝓝 x₀, W ⊆ V ∧ ∀ (k : G) (x : E), x ∈ W → ρ k x ∈ W := by
  obtain ⟨V', hV'V, hV'o, hxV'⟩ := mem_nhds_iff.mp hV
  have hcont : Continuous fun p : E × G => ρ p.2 p.1 :=
    hρ.comp (continuous_snd.prodMk continuous_fst)
  have hev : ∀ k ∈ (univ : Set G), ∀ᶠ z : E × G in 𝓝 (x₀, k), ρ z.2 z.1 ∈ V' := by
    intro k _
    have hopen : IsOpen {z : E × G | ρ z.2 z.1 ∈ V'} := hV'o.preimage hcont
    exact hopen.mem_nhds (by change ρ k x₀ ∈ V'; rw [hx₀ k]; exact hxV')
  have hW := IsCompact.eventually_forall_of_forall_eventually (P := fun (x : E) (k : G) => ρ k x ∈ V')
    isCompact_univ hev
  refine ⟨{x | ∀ k : G, ρ k x ∈ V'}, ?_, ?_, ?_⟩
  · exact hW.mono fun x hx k => hx k (mem_univ k)
  · intro x hx
    have h1 := hx 1
    rw [map_one, ContinuousLinearMap.one_apply] at h1
    exact hV'V h1
  · intro k x hx k'
    rw [← ContinuousLinearMap.mul_apply, ← map_mul]
    exact hx (k' * k)

section Measure

theorem abs_det_rho_le_one (μ : Measure E) [μ.IsAddHaarMeasure] (hρ : Continuous fun p : G × E => ρ p.1 p.2) (k : G) :
    |LinearMap.det (ρ k : E →ₗ[ℝ] E)| ≤ 1 := by

  set C : Set E := (fun p : G × E => ρ p.1 p.2) '' (univ ×ˢ Metric.closedBall (0 : E) 1) with hC_def
  have hCc : IsCompact C := (isCompact_univ.prod (isCompact_closedBall (0 : E) 1)).image hρ
  have hBC : Metric.closedBall (0 : E) 1 ⊆ C := fun x hx =>
    ⟨(1, x), ⟨mem_univ _, hx⟩, by simp only [map_one, ContinuousLinearMap.one_apply]⟩
  have hCpos : 0 < μ C := lt_of_lt_of_le (Metric.measure_closedBall_pos μ (0 : E) one_pos) (measure_mono hBC)
  have hCtop : μ C < ⊤ := hCc.measure_lt_top
  have himg : (ρ k : E →ₗ[ℝ] E) '' C ⊆ C := by
    rintro _ ⟨_, ⟨⟨k', x⟩, ⟨-, hx⟩, rfl⟩, rfl⟩
    refine ⟨(k * k', x), ⟨mem_univ _, hx⟩, ?_⟩
    change ρ (k * k') x = ρ k (ρ k' x)
    rw [map_mul, ContinuousLinearMap.mul_apply]
  have hle : ENNReal.ofReal |LinearMap.det (ρ k : E →ₗ[ℝ] E)| * μ C ≤ 1 * μ C := by
    rw [← Measure.addHaar_image_linearMap μ (ρ k : E →ₗ[ℝ] E) C, one_mul]
    exact measure_mono himg
  have h1 : ENNReal.ofReal |LinearMap.det (ρ k : E →ₗ[ℝ] E)| ≤ 1 :=
    (ENNReal.mul_le_mul_iff_left hCpos.ne' hCtop.ne).mp hle
  exact ENNReal.ofReal_le_one.mp h1

theorem abs_det_rho_eq_one (μ : Measure E) [μ.IsAddHaarMeasure] (hρ : Continuous fun p : G × E => ρ p.1 p.2) (k : G) :
    |LinearMap.det (ρ k : E →ₗ[ℝ] E)| = 1 := by
  have h1 := abs_det_rho_le_one ρ μ hρ k
  have h2 := abs_det_rho_le_one ρ μ hρ k⁻¹
  have hprod : |LinearMap.det (ρ k : E →ₗ[ℝ] E)| * |LinearMap.det (ρ k⁻¹ : E →ₗ[ℝ] E)| = 1 := by
    rw [← abs_mul, ← LinearMap.det_comp, ← ContinuousLinearMap.toLinearMap_comp, ← ContinuousLinearMap.mul_def,
      ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id,
      LinearMap.det_id, abs_one]
  nlinarith [abs_nonneg (LinearMap.det (ρ k : E →ₗ[ℝ] E)), abs_nonneg (LinearMap.det (ρ k⁻¹ : E →ₗ[ℝ] E))]

theorem map_rho_eq (μ : Measure E) [μ.IsAddHaarMeasure] (hρ : Continuous fun p : G × E => ρ p.1 p.2) (k : G) : Measure.map (ρ k) μ = μ := by
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar μ (det_rho_ne_zero ρ k)
  rw [abs_inv, abs_det_rho_eq_one ρ μ hρ k, inv_one, ENNReal.ofReal_one, one_smul] at h
  exact h

theorem integral_comp_rho (μ : Measure E) [μ.IsAddHaarMeasure] (hρ : Continuous fun p : G × E => ρ p.1 p.2) (k : G) {H : E → ℂ}
    (hH : Continuous H) : ∫ x, H (ρ k x) ∂μ = ∫ y, H y ∂μ := by
  have h := MeasureTheory.integral_map (μ := μ) (ρ k).continuous.aemeasurable
    (hH.aestronglyMeasurable (μ := Measure.map (ρ k) μ))
  rw [map_rho_eq ρ μ hρ k] at h
  exact h.symm

end Measure

section Average

variable [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν]

def avg (g : E → ℂ) (y : E) : ℂ := ∫ k, g (ρ k⁻¹ y) ∂ν

theorem continuous_uncurry_comp_inv (hρ : Continuous fun p : G × E => ρ p.1 p.2) {g : E → ℂ}
    (hg : Continuous g) : Continuous (Function.uncurry fun (y : E) (k : G) => g (ρ k⁻¹ y)) :=
  hg.comp (hρ.comp ((continuous_inv.comp continuous_snd).prodMk continuous_fst))

theorem continuous_avg (hρ : Continuous fun p : G × E => ρ p.1 p.2) {g : E → ℂ} (hg : Continuous g) :
    Continuous (avg ρ ν g) := by
  have h := continuous_parametric_integral_of_continuous (μ := ν)
    (continuous_uncurry_comp_inv ρ hρ hg) isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

def hull (g : E → ℂ) : Set E := (fun p : G × E => ρ p.1 p.2) '' (univ ×ˢ tsupport g)

theorem isCompact_hull (hρ : Continuous fun p : G × E => ρ p.1 p.2) {g : E → ℂ} (hg : HasCompactSupport g) :
    IsCompact (hull ρ g) :=
  (isCompact_univ.prod hg).image hρ

theorem apply_comp_inv_eq_zero_of_notMem_hull {g : E → ℂ} {y : E} (hy : y ∉ hull ρ g) (k : G) :
    g (ρ k⁻¹ y) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hy ⟨(k, ρ k⁻¹ y), ⟨mem_univ _, hmem⟩, rho_apply_inv ρ k y⟩

theorem support_avg_subset (g : E → ℂ) : Function.support (avg ρ ν g) ⊆ hull ρ g := by
  intro y hy
  by_contra hy'
  apply hy
  change ∫ k, g (ρ k⁻¹ y) ∂ν = 0
  simp only [apply_comp_inv_eq_zero_of_notMem_hull ρ hy', integral_zero]

theorem hasCompactSupport_avg (hρ : Continuous fun p : G × E => ρ p.1 p.2) {g : E → ℂ}
    (hg : HasCompactSupport g) : HasCompactSupport (avg ρ ν g) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_hull ρ hρ hg) (support_avg_subset ρ ν g)

theorem tsupport_avg_subset (hρ : Continuous fun p : G × E => ρ p.1 p.2) {g : E → ℂ}
    (hg : HasCompactSupport g) : tsupport (avg ρ ν g) ⊆ hull ρ g :=
  closure_minimal (support_avg_subset ρ ν g) (isCompact_hull ρ hρ hg).isClosed

theorem hull_subset {g : E → ℂ} {W : Set E} (hgW : tsupport g ⊆ W) (hW : ∀ (k : G) (x : E), x ∈ W → ρ k x ∈ W) :
    hull ρ g ⊆ W := by
  rintro _ ⟨⟨k, x⟩, ⟨-, hx⟩, rfl⟩
  exact hW k x (hgW hx)

theorem avg_rho_apply [MeasurableMul G] [ν.IsMulLeftInvariant] (g : E → ℂ) (k₀ : G) (y : E) :
    avg ρ ν g (ρ k₀ y) = avg ρ ν g y := by
  change ∫ k, g (ρ k⁻¹ (ρ k₀ y)) ∂ν = ∫ k, g (ρ k⁻¹ y) ∂ν
  have h : ∀ k : G, g (ρ k⁻¹ (ρ k₀ y)) = (fun k' : G => g (ρ k'⁻¹ y)) (k₀⁻¹ * k) := by
    intro k
    simp only [mul_inv_rev, inv_inv, map_mul, ContinuousLinearMap.mul_apply]
  simp_rw [h]
  exact integral_mul_left_eq_self (fun k' : G => g (ρ k'⁻¹ y)) k₀⁻¹

end Average

theorem main (μ : Measure E) [μ.IsAddHaarMeasure]
    (hρ : Continuous fun p : G × E => ρ p.1 p.2)
    (x₀ : E) (hx₀ : ∀ k : G, ρ k x₀ = x₀)
    (D : (E → ℂ) → (E → ℂ))
    (hDc : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → Continuous (D F))
    (hDρ : ∀ (k : G) (F : E → ℂ), ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      D (fun x => F (ρ k x)) = fun x => D F (ρ k x))
    (hex : ∀ W ∈ 𝓝 x₀, ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ W ∧ tsupport g₂ ⊆ W ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, D F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ)
    (V : Set E) (hV : V ∈ 𝓝 x₀) :
    ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ V ∧ tsupport g₂ ⊆ V ∧
      (∀ (k : G) (x : E), g₁ (ρ k x) = g₁ x) ∧ (∀ (k : G) (x : E), g₂ (ρ k x) = g₂ x) ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, D F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ := by

  letI mG : MeasurableSpace G := borel G
  haveI bG : BorelSpace G := ⟨rfl⟩
  let ν : Measure G := Measure.haarMeasure ⊤
  have hν1 : ν univ = 1 := by
    change Measure.haarMeasure ⊤ ((⊤ : TopologicalSpace.PositiveCompacts G) : Set G) = 1
    exact Measure.haarMeasure_self
  haveI : IsProbabilityMeasure ν := ⟨hν1⟩

  obtain ⟨W, hW, hWV, hWst⟩ := exists_stable_nhds ρ hρ x₀ hx₀ hV
  obtain ⟨g₁, g₂, hg₁c, hg₂c, hg₁s, hg₂s, hg₁W, hg₂W, hid⟩ := hex W hW

  refine ⟨avg ρ ν g₁, avg ρ ν g₂, continuous_avg ρ ν hρ hg₁c, continuous_avg ρ ν hρ hg₂c,
    hasCompactSupport_avg ρ ν hρ hg₁s, hasCompactSupport_avg ρ ν hρ hg₂s,
    (tsupport_avg_subset ρ ν hρ hg₁s).trans ((hull_subset ρ hg₁W hWst).trans hWV),
    (tsupport_avg_subset ρ ν hρ hg₂s).trans ((hull_subset ρ hg₂W hWst).trans hWV),
    avg_rho_apply ρ ν g₁, avg_rho_apply ρ ν g₂, ?_⟩
  intro F hF hFc
  have hDF : Continuous (D F) := hDc F hF hFc
  have hFcont : Continuous F := hF.continuous

  have hk : ∀ k : G, F x₀ = (∫ y, D F y * g₁ (ρ k⁻¹ y) ∂μ) + ∫ y, F y * g₂ (ρ k⁻¹ y) ∂μ := by
    intro k
    have hFks : ContDiff ℝ (⊤ : ℕ∞) (fun x => F (ρ k x)) := hF.comp (ρ k).contDiff
    have hFkc : HasCompactSupport (fun x => F (ρ k x)) := hFc.comp_homeomorph (rhoEquiv ρ k).toHomeomorph
    have h1 := hid (fun x => F (ρ k x)) hFks hFkc
    rw [hx₀ k, hDρ k F hF hFc] at h1
    have e1 : ∫ x, D F (ρ k x) * g₁ x ∂μ = ∫ y, D F y * g₁ (ρ k⁻¹ y) ∂μ := by
      have := integral_comp_rho ρ μ hρ k (H := fun y => D F y * g₁ (ρ k⁻¹ y))
        (hDF.mul (hg₁c.comp (ρ k⁻¹).continuous))
      simp only [rho_inv_apply] at this
      exact this
    have e2 : ∫ x, F (ρ k x) * g₂ x ∂μ = ∫ y, F y * g₂ (ρ k⁻¹ y) ∂μ := by
      have := integral_comp_rho ρ μ hρ k (H := fun y => F y * g₂ (ρ k⁻¹ y))
        (hFcont.mul (hg₂c.comp (ρ k⁻¹).continuous))
      simp only [rho_inv_apply] at this
      exact this
    rw [e1, e2] at h1
    exact h1

  have hint : ∀ {A g : E → ℂ}, Continuous A → Continuous g → HasCompactSupport g →
      Integrable (Function.uncurry fun (k : G) (y : E) => A y * g (ρ k⁻¹ y)) (ν.prod μ) := by
    intro A g hA hg hgs
    have hcont : Continuous (Function.uncurry fun (k : G) (y : E) => A y * g (ρ k⁻¹ y)) :=
      (hA.comp continuous_snd).mul (hg.comp (hρ.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd)))
    have hsupp : Function.support (Function.uncurry fun (k : G) (y : E) => A y * g (ρ k⁻¹ y)) ⊆
        univ ×ˢ hull ρ g := by
      intro p hp
      refine ⟨mem_univ _, ?_⟩
      by_contra hy
      apply hp
      change A p.2 * g (ρ p.1⁻¹ p.2) = 0
      rw [apply_comp_inv_eq_zero_of_notMem_hull ρ hy p.1, mul_zero]
    have hcs : HasCompactSupport (Function.uncurry fun (k : G) (y : E) => A y * g (ρ k⁻¹ y)) :=
      HasCompactSupport.of_support_subset_isCompact (isCompact_univ.prod (isCompact_hull ρ hρ hgs)) hsupp
    exact hcont.integrable_of_hasCompactSupport hcs
  have hswap : ∀ {A g : E → ℂ}, Continuous A → Continuous g → HasCompactSupport g →
      ∫ k, ∫ y, A y * g (ρ k⁻¹ y) ∂μ ∂ν = ∫ y, A y * avg ρ ν g y ∂μ := by
    intro A g hA hg hgs
    rw [integral_integral_swap (hint hA hg hgs)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    change ∫ k, A y * g (ρ k⁻¹ y) ∂ν = A y * ∫ k, g (ρ k⁻¹ y) ∂ν
    exact integral_const_mul _ _
  have hI1 : Integrable (fun k : G => ∫ y, D F y * g₁ (ρ k⁻¹ y) ∂μ) ν := (hint hDF hg₁c hg₁s).integral_prod_left
  have hI2 : Integrable (fun k : G => ∫ y, F y * g₂ (ρ k⁻¹ y) ∂μ) ν := (hint hFcont hg₂c hg₂s).integral_prod_left
  calc F x₀ = ∫ _k : G, F x₀ ∂ν := by
        rw [integral_const, probReal_univ, one_smul]
    _ = ∫ k, ((∫ y, D F y * g₁ (ρ k⁻¹ y) ∂μ) + ∫ y, F y * g₂ (ρ k⁻¹ y) ∂μ) ∂ν :=
        integral_congr_ae (Eventually.of_forall hk)
    _ = (∫ k, ∫ y, D F y * g₁ (ρ k⁻¹ y) ∂μ ∂ν) + ∫ k, ∫ y, F y * g₂ (ρ k⁻¹ y) ∂μ ∂ν := integral_add hI1 hI2
    _ = (∫ y, D F y * avg ρ ν g₁ y ∂μ) + ∫ y, F y * avg ρ ν g₂ y ∂μ := by
        rw [hswap hDF hg₁c hg₁s, hswap hFcont hg₂c hg₂s]

end R4KAvg
p2m_reactivate "P2MW.S_LocalParametrix_exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace.R4KAvg"

end
p2m_reactivate "P2MW.S_LocalParametrix_exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace.R4KAvg"

open MeasureTheory Topology

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (ρ : G →* (E →L[ℝ] E)) (hρ : Continuous fun p : G × E => ρ p.1 p.2)
    (x₀ : E) (hx₀ : ∀ k : G, ρ k x₀ = x₀)
    (D : (E → ℂ) → (E → ℂ))
    (hDc : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → Continuous (D F))
    (hDρ : ∀ (k : G) (F : E → ℂ), ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      D (fun x => F (ρ k x)) = fun x => D F (ρ k x))
    (hex : ∀ W ∈ 𝓝 x₀, ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ W ∧ tsupport g₂ ⊆ W ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, D F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ)
    (V : Set E) (hV : V ∈ 𝓝 x₀) :
    ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ V ∧ tsupport g₂ ⊆ V ∧
      (∀ (k : G) (x : E), g₁ (ρ k x) = g₁ x) ∧ (∀ (k : G) (x : E), g₂ (ρ k x) = g₂ x) ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, D F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ :=
  R4KAvg.main ρ μ hρ x₀ hx₀ D hDc hDρ hex V hV

end S_LocalParametrix_exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace
end P2MW
export P2MW.S_LocalParametrix_exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace (solution)

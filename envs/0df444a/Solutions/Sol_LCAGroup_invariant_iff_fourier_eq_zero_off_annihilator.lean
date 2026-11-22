-- Prove2me | solution 1 for LCAGroup.invariant_iff_fourier_eq_zero_off_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:36:37.424794+00:00
-- url     : https://prove2.me/submissions/08a1f969-31be-4ce9-9e84-6eed23fea77e

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Definitions.Def_LCAGroup_Annihilator
import Theorems.Thm_LCAGroup_fourier_L1_to_zeroAtInfty_injective

open MeasureTheory Topology

set_option autoImplicit false

namespace Sol_LCAGroup_invariant_iff_fourier_eq_zero_off_annihilator

/-- `conj (χ h) * χ h = 1` for a character with values in the circle. -/
theorem star_mul_self_circle (z : Circle) : star (z : ℂ) * (z : ℂ) = 1 := by
  have h1 : star (z : ℂ) = ((z⁻¹ : Circle) : ℂ) := by
    rw [Circle.coe_inv_eq_conj]; rfl
  rw [h1, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]

/-- The Fourier transform of a right translate: `(f(· h))^(χ) = χ(h) f^(χ)`. -/
theorem fourier_translate {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant] (f : G → ℂ) (h : G)
    (χ : PontryaginDual G) :
    RiemannMasullo.lcaFourier μ (fun x => f (x * h)) χ =
      (χ h : ℂ) * RiemannMasullo.lcaFourier μ f χ := by
  unfold RiemannMasullo.lcaFourier
  have key : ∀ x : G, f (x * h) * star (χ x : ℂ) =
      (χ h : ℂ) * (f (x * h) * star (χ (x * h) : ℂ)) := by
    intro x
    rw [map_mul, Circle.coe_mul, star_mul']
    have := star_mul_self_circle (χ h)
    calc f (x * h) * star (χ x : ℂ)
        = f (x * h) * star (χ x : ℂ) * (star (χ h : ℂ) * (χ h : ℂ)) := by rw [this, mul_one]
      _ = (χ h : ℂ) * (f (x * h) * (star (χ x : ℂ) * star (χ h : ℂ))) := by ring
  simp_rw [key]
  rw [integral_const_mul]
  congr 1
  exact integral_mul_right_eq_self (fun y => f y * star (χ y : ℂ)) h

end Sol_LCAGroup_invariant_iff_fourier_eq_zero_off_annihilator

open Sol_LCAGroup_invariant_iff_fourier_eq_zero_off_annihilator in
open LCAGroup in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure] [ν.Regular]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (f : G → ℂ) (hf : Integrable f μ) :
    ((∀ x : G, ∀ h ∈ H, f (x * h) = f x) →
      ∀ χ : PontryaginDual G, χ ∉ annihilator H → RiemannMasullo.lcaFourier μ f χ = 0) ∧
    (Continuous f → Integrable (RiemannMasullo.lcaFourier μ f) ν →
      (∀ χ : PontryaginDual G, χ ∉ annihilator H → RiemannMasullo.lcaFourier μ f χ = 0) →
      ∀ x : G, ∀ h ∈ H, f (x * h) = f x) := by
  refine ⟨?_, ?_⟩
  · -- Part 1: invariance forces the Fourier transform to vanish off the annihilator.
    intro hinv χ hχ
    rw [mem_annihilator_iff] at hχ
    push_neg at hχ
    obtain ⟨h, hhH, hχh⟩ := hχ
    have hfun : (fun x => f (x * h)) = f := funext fun x => hinv x h hhH
    have htr := fourier_translate μ f h χ
    rw [hfun] at htr
    have hne : (χ h : ℂ) ≠ 1 := fun e => hχh (Circle.coe_eq_one.mp e)
    have h0 : (1 - (χ h : ℂ)) * RiemannMasullo.lcaFourier μ f χ = 0 := by
      rw [sub_mul, one_mul, ← htr, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1).symm hne
    · exact h1
  · -- Part 2: injectivity of the Fourier transform on `L¹`.
    intro hcont _ hvan x h hhH
    set g : G → ℂ := fun y => f (y * h) with hg_def
    have hg : Integrable g μ := hf.comp_mul_right h
    have hgc : Continuous g := hcont.comp (continuous_id.mul continuous_const)
    have hfour : ∀ χ : PontryaginDual G,
        RiemannMasullo.lcaFourier μ g χ = RiemannMasullo.lcaFourier μ f χ := by
      intro χ
      rw [hg_def, fourier_translate μ f h χ]
      by_cases hχ : χ ∈ annihilator H
      · rw [(mem_annihilator_iff H χ).mp hχ h hhH, Circle.coe_one, one_mul]
      · rw [hvan χ hχ, mul_zero]
    obtain ⟨F, hF, hFinj, -⟩ := LCAGroup.fourier_L1_to_zeroAtInfty_injective G μ
    have hcongr : ∀ (u : G → ℂ) (hu : Integrable u μ) (χ : PontryaginDual G),
        RiemannMasullo.lcaFourier μ ((hu.toL1 u : Lp ℂ 1 μ) : G → ℂ) χ =
          RiemannMasullo.lcaFourier μ u χ := by
      intro u hu χ
      unfold RiemannMasullo.lcaFourier
      refine integral_congr_ae ?_
      filter_upwards [hu.coeFn_toL1] with y hy
      rw [hy]
    have hFeq : F (hg.toL1 g) = F (hf.toL1 f) := by
      ext χ
      rw [hF, hF, hcongr g hg χ, hcongr f hf χ, hfour χ]
    have hL1 : hg.toL1 g = hf.toL1 f := hFinj hFeq
    have hae : g =ᵐ[μ] f := (Integrable.toL1_eq_toL1_iff g f hg hf).mp hL1
    have hgf : g = f := (hgc.ae_eq_iff_eq μ hcont).mp hae
    exact congrFun hgf x

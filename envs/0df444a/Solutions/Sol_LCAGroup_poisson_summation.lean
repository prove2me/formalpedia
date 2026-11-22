-- Prove2me | solution 1 for LCAGroup.poisson_summation
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T13:02:49.138892+00:00
-- url     : https://prove2.me/submissions/6ed4fef8-f60c-43cd-9f1e-4e0b02ddf18d

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Definitions.Def_LCAGroup_PlancherelMeasure
import Theorems.Thm_LCAGroup_weil_quotient_integral_formula
import Theorems.Thm_LCAGroup_fourier_inversion

open MeasureTheory Topology

set_option autoImplicit false

namespace Sol_LCAGroup_poisson_summation

/-- By left invariance of the Haar measure of `H`, the fibre integral over the coset of `x` does not
depend on the representative: the chosen representative `(x H).out` may be replaced by `x`.
No integrability is needed. -/
theorem cosetIntegral_mk {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [μH.IsHaarMeasure] (f : G → ℂ) (x : G) :
    (∫ h : H, f ((QuotientGroup.mk x : G ⧸ H).out * (h : G)) ∂μH) =
      ∫ h : H, f (x * (h : G)) ∂μH := by
  set y : G := Quotient.out (QuotientGroup.mk x : G ⧸ H) with hydef
  have hy : (QuotientGroup.mk y : G ⧸ H) = QuotientGroup.mk x := Quotient.out_eq' _
  have hk : y⁻¹ * x ∈ H := QuotientGroup.eq.mp hy
  let k : H := ⟨y⁻¹ * x, hk⟩
  have hxe : x = y * (k : G) := by
    simp [k]
  have hassoc : ∀ h : H, x * (h : G) = y * ((k * h : H) : G) := by
    intro h
    rw [Subgroup.coe_mul, ← mul_assoc, ← hxe]
  simp_rw [hassoc]
  exact (MeasureTheory.integral_mul_left_eq_self (fun h : H ↦ f (y * (h : G))) k).symm

/-- The coset of `q.out * h` is `q` for `h ∈ H`. -/
theorem mk_out_mul {G : Type*} [Group G] (H : Subgroup G) (q : G ⧸ H) (h : H) :
    ((q.out * (h : G) : G) : G ⧸ H) = q := by
  have h1 : ((q.out * (h : G) : G) : G ⧸ H) = (q.out : G ⧸ H) :=
    (QuotientGroup.mk_mul_of_mem (s := H) q.out h.2)
  rw [h1]
  exact Quotient.out_eq' q

/-- Multiplication by the conjugate of a character of the quotient, pulled back to `G`,
preserves integrability. -/
theorem integrable_mul_star_char {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
    (μ : Measure G) {f : G → ℂ} (hf : Integrable f μ) (η : PontryaginDual (G ⧸ H)) :
    Integrable (fun x : G => f x * star (η (x : G ⧸ H) : ℂ)) μ := by
  have hc : Continuous fun x : G => star (η (x : G ⧸ H) : ℂ) :=
    (continuous_subtype_val.comp (η.continuous.comp QuotientGroup.continuous_mk)).star
  exact hf.mul_bdd (c := 1) hc.aestronglyMeasurable
    (.of_forall fun x ↦ by rw [norm_star, Circle.norm_coe])

end Sol_LCAGroup_poisson_summation

open LCAGroup Sol_LCAGroup_poisson_summation in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    [MeasurableSpace (PontryaginDual (G ⧸ H))] [BorelSpace (PontryaginDual (G ⧸ H))]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
    (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure] [ν.Regular]
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν)
    (ν' : Measure (PontryaginDual (G ⧸ H))) (hν' : IsPlancherelMeasure ν ν')
    (f : G → ℂ) (hf : Integrable f μ) :
    (∀ η : PontryaginDual (G ⧸ H),
      RiemannMasullo.lcaFourier ν (fun q : G ⧸ H => ∫ h : H, f (q.out * (h : G)) ∂μH) η =
        ∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) ∧
    (Integrable (fun η : PontryaginDual (G ⧸ H) =>
        ∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) ν' →
      (∀ᵐ q ∂ν, ∫ h : H, f (q.out * (h : G)) ∂μH =
        ∫ η : PontryaginDual (G ⧸ H),
          (∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) * (η q : ℂ) ∂ν') ∧
      ((∀ y : G, Integrable (fun h : H => f (y * (h : G))) μH) →
        Continuous (fun y : G => ∫ h : H, f (y * (h : G)) ∂μH) →
        ∀ y : G, ∫ h : H, f (y * (h : G)) ∂μH =
          ∫ η : PontryaginDual (G ⧸ H),
            (∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) * (η (y : G ⧸ H) : ℂ) ∂ν')) := by
  have : IsClosed (H : Set G) := hH
  -- Part 1: Weil's formula for `x ↦ f x * conj (η (x H))`.
  have h1 : ∀ η : PontryaginDual (G ⧸ H),
      RiemannMasullo.lcaFourier ν (fun q : G ⧸ H => ∫ h : H, f (q.out * (h : G)) ∂μH) η =
        ∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ := by
    intro η
    obtain ⟨-, -, hW⟩ := LCAGroup.weil_quotient_integral_formula G H hH μ μH ν hν
      (fun x : G => f x * star (η (x : G ⧸ H) : ℂ)) (integrable_mul_star_char H μ hf η)
    rw [hW]
    unfold RiemannMasullo.lcaFourier
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    change (∫ h : H, f (q.out * (h : G)) ∂μH) * star (η q : ℂ) =
      ∫ h : H, f (q.out * (h : G)) * star (η ((q.out * (h : G) : G) : G ⧸ H) : ℂ) ∂μH
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    change f (q.out * (h : G)) * star (η q : ℂ) =
      f (q.out * (h : G)) * star (η ((q.out * (h : G) : G) : G ⧸ H) : ℂ)
    rw [mk_out_mul H q h]
  refine ⟨h1, fun hint => ?_⟩
  -- The fibre integral `f^H` is integrable on `G ⧸ H`, and so is its Fourier transform.
  obtain ⟨-, hFint, -⟩ := LCAGroup.weil_quotient_integral_formula G H hH μ μH ν hν f hf
  have hfun : RiemannMasullo.lcaFourier ν (fun q : G ⧸ H => ∫ h : H, f (q.out * (h : G)) ∂μH) =
      fun η : PontryaginDual (G ⧸ H) => ∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ :=
    funext h1
  have hF' : Integrable
      (RiemannMasullo.lcaFourier ν (fun q : G ⧸ H => ∫ h : H, f (q.out * (h : G)) ∂μH)) ν' := by
    rw [hfun]
    exact hint
  -- Fourier inversion on `G ⧸ H`.
  obtain ⟨hae, hcont⟩ := LCAGroup.fourier_inversion (G ⧸ H) ν ν' hν'
    (fun q : G ⧸ H => ∫ h : H, f (q.out * (h : G)) ∂μH) hFint hF'
  rw [hfun] at hae hcont
  refine ⟨hae, fun _ hc y => ?_⟩
  -- Part 3: `f^H` is continuous on `G ⧸ H` because its pull-back to `G` is.
  have hcomp : (fun q : G ⧸ H => ∫ h : H, f (q.out * (h : G)) ∂μH) ∘ (QuotientGroup.mk : G → G ⧸ H) =
      fun y : G => ∫ h : H, f (y * (h : G)) ∂μH :=
    funext fun y => cosetIntegral_mk H μH f y
  have hFc : Continuous (fun q : G ⧸ H => ∫ h : H, f (q.out * (h : G)) ∂μH) := by
    rw [(QuotientGroup.isQuotientMap_mk H).continuous_iff, hcomp]
    exact hc
  have hy := hcont hFc (y : G ⧸ H)
  rw [← cosetIntegral_mk H μH f y]
  exact hy

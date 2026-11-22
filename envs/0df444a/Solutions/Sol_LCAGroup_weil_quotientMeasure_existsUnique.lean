-- Prove2me | solution 1 for LCAGroup.weil_quotientMeasure_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:16:49.355081+00:00
-- url     : https://prove2.me/submissions/70ff73c6-e987-4923-8e12-cdc29dd3c410

import Mathlib

open MeasureTheory Topology

set_option autoImplicit false

namespace Sol_LCAGroup_weil_quotientMeasure_existsUnique

/-- Complex compactly supported test functions integrate against the induced Haar measure of a
short exact sequence by integrating first over the subgroup and then over the quotient
(Mathlib states this for real test functions: `TopologicalGroup.IsSES.integral_inducedMeasure`). -/
theorem integral_inducedMeasure_complex {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
    [LocallyCompactSpace B] [T2Space B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B]
    [MeasurableSpace C] [BorelSpace C]
    {i : A →* B} {p : B →* C} (h : TopologicalGroup.IsSES i p)
    (μA : Measure A) [μA.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure]
    (f : CompactlySupportedContinuousMap B ℂ) :
    ∫ b, f b ∂(h.inducedMeasure μA μC) = h.integrate μA μC f := by
  have test (L : ℂ →L[ℝ] ℝ) :
      L (∫ b, f b ∂(h.inducedMeasure μA μC)) = L (h.integrate μA μC f) := by
    let ℓ : C(ℂ, ℝ) := ⟨L, L.continuous⟩
    let g := f.compLeft ℓ
    have hg (b : B) : g b = L (f b) :=
      CompactlySupportedContinuousMap.compLeft_apply (g := ℓ) L.map_zero f b
    rw [← L.integral_comp_comm f.integrable, h.integrate_apply,
      ← L.integral_comp_comm (h.pushforward μA f).integrable]
    simp_rw [← hg]
    rw [h.integral_inducedMeasure, h.integrate_apply]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro c
    obtain ⟨b, rfl⟩ := h.isOpenQuotientMap.surjective c
    change h.pushforward μA g (p b) = L (h.pushforward μA f (p b))
    rw [h.pushforward_apply_apply, h.pushforward_apply_apply,
      ← L.integral_comp_comm (h.pullback f b).integrable]
    simp only [h.pullback_def, hg]
  exact Complex.ext (test Complex.reCLM) (test Complex.imCLM)

/-- The fibre integral computed at the chosen representative `Quotient.out` of the coset of `x`
agrees with the fibre integral computed at `x` (left invariance of the Haar measure of `H`). -/
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

end Sol_LCAGroup_weil_quotientMeasure_existsUnique

open Sol_LCAGroup_weil_quotientMeasure_existsUnique in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular] :
    ∃! ν : Measure (G ⧸ H), ν.IsHaarMeasure ∧ ν.Regular ∧
      ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
        ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν := by
  have : IsClosed (H : Set G) := hH
  have h : TopologicalGroup.IsSES H.subtype (QuotientGroup.mk' H) :=
    TopologicalGroup.IsSES.ofClosedSubgroup H hH
  -- a reference Haar measure on the quotient and the Haar measure it induces on `G`
  let ν₀ : Measure (G ⧸ H) := MeasureTheory.Measure.haar
  let μ₀ : Measure G := h.inducedMeasure μH ν₀
  let c := Measure.haarScalarFactor μ μ₀
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne'
  have hμ : μ = c • μ₀ := Measure.isMulLeftInvariant_eq_smul_of_regular μ μ₀
  let ν : Measure (G ⧸ H) := c • ν₀
  have hνH : ν.IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul ν₀ hc
  have hνR : ν.Regular := Measure.Regular.smul_nnreal c
  -- Weil's formula for `ν`
  have hformula : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν := by
    intro φ hφ hφc
    let f' : CompactlySupportedContinuousMap G ℂ := ⟨⟨φ, hφ⟩, hφc⟩
    have hfib (q : G ⧸ H) :
        h.pushforward μH f' q = ∫ k : H, φ (q.out * (k : G)) ∂μH := by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      change h.pushforward μH f' ((QuotientGroup.mk' H) x) = _
      rw [h.pushforward_apply_apply]
      exact (cosetIntegral_mk H μH φ x).symm
    change (∫ x, f' x ∂μ) = ∫ q : G ⧸ H, (∫ k : H, φ (q.out * (k : G)) ∂μH) ∂(c • ν₀)
    rw [hμ, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      integral_inducedMeasure_complex h μH ν₀ f', h.integrate_apply]
    simp_rw [hfib]
  refine ⟨ν, ⟨hνH, hνR, hformula⟩, ?_⟩
  -- uniqueness: two regular Haar measures differ by a scalar, fixed by one test function
  rintro ν' ⟨hν'H, hν'R, hν'⟩
  let d := Measure.haarScalarFactor ν' ν
  have hνeq : ν' = d • ν := Measure.isMulLeftInvariant_eq_smul_of_regular ν' ν
  obtain ⟨g, hg, hnonneg, hpos⟩ := exists_continuous_nonneg_pos (1 : G)
  let f : G → ℂ := fun x ↦ (g x : ℂ)
  have hfcont : Continuous f := Complex.continuous_ofReal.comp g.continuous
  have hf : HasCompactSupport f := hg.comp_left Complex.ofReal_zero
  have hI : (∫ x, f x ∂μ) ≠ 0 := by
    change (∫ x, (g x : ℂ) ∂μ) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr
      (g.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hg hnonneg hpos).ne'
  have hscalar := hν' f hfcont hf
  rw [hνeq, integral_smul_nnreal_measure, ← hformula f hfcont hf] at hscalar
  have hunit : d = 1 := by
    have he : (1 : ℂ) * (∫ x, f x ∂μ) = ((d : ℝ) : ℂ) * (∫ x, f x ∂μ) := by
      simpa only [one_mul, NNReal.smul_def, Complex.real_smul] using hscalar
    exact_mod_cast (mul_right_cancel₀ hI he).symm
  rw [hνeq, hunit, one_smul]

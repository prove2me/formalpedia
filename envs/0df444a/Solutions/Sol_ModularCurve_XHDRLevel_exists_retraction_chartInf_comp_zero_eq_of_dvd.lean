-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_retraction_chartInf_comp_zero_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a2af07da-3b60-5281-b201-f3ba2f1f6b15

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_retraction_chartInf_comp_zero_eq_of_dvd

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel NeronModelInfra
open scoped MatrixGroups TensorProduct

namespace RetractInfH

theorem range_subset_of_isOpen {A : Type} [CommRing A] [IsLocalRing A] {Y : Scheme.{0}}
    (f : Spec (CommRingCat.of A) ⟶ Y) {U : Set Y} (hU : IsOpen U)
    (h : f (IsLocalRing.closedPoint A) ∈ U) : Set.range f ⊆ U := by
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map f.continuous).mem_open hU h

section Chart

variable (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (κ : Type) [CommRing κ] [Algebra (R p) κ]

theorem isPullback_chart
    (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p Γ hj))) ⟶
      pullback (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj))).toRingHom) ≫ ιInf p Γ hj)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj))))) :
    IsPullback c (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj))).toRingHom)) (pullback.fst _ _) (ιInf p Γ hj) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd _ _)
    (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap (R p) κ))) (h₂₂ := toBase p Γ hj) ?_ hcfst
    (IsPullback.of_hasPullback _ _).flip
  rw [hcsnd, TwoChartIntegralModel.ιInf_toBase]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct (R p) κ ↥(chartAlgInf p Γ hj))

theorem isOpenImmersion_chart
    (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p Γ hj))) ⟶
      pullback (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj))).toRingHom) ≫ ιInf p Γ hj)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj))))) :
    IsOpenImmersion c := by
  rw [← (isPullback_chart p Γ hj κ c hcfst hcsnd).isoPullback_hom_fst]
  infer_instance

theorem mem_range_chart
    (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p Γ hj))) ⟶
      pullback (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj))).toRingHom) ≫ ιInf p Γ hj)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj)))))
    (x : ↥(pullback (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))))
    (hx : (pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) x ∈ Set.range (ιInf p Γ hj)) :
    x ∈ Set.range c := by
  have H := isPullback_chart p Γ hj κ c hcfst hcsnd
  have hx' : x ∈ Set.range (pullback.fst (pullback.fst (toBase p Γ hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) (ιInf p Γ hj)) := by
    rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨t, rfl⟩ := hx'
  exact ⟨H.isoPullback.inv t, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst]⟩

end Chart

section Key

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

theorem iotaInf_jInvChartInf
    (iotaInf : ↥(chartAlgInf p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj))
    (iotaInf_spec : ∀ b, (((iotaInf b : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) :
    iotaInf (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) =
      TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) := by
  apply Subtype.ext; apply Subtype.ext
  rw [iotaInf_spec, TwoChartIntegralModel.coe_jInvChartInf, TwoChartIntegralModel.coe_jInvChartInf]
  simp [jAt]

theorem specMap_val_ιFin (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Spec.map (CommRingCat.ofHom (chartAlgFin p Γ hj).val.toRingHom) ≫ ιFin p Γ hj =
      Spec.map (CommRingCat.ofHom (chartAlgInf p Γ hj).val.toRingHom) ≫ ιInf p Γ hj := by
  have h1 : (chartAlgInf p Γ hj).val.toRingHom =
      (TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)).val.toRingHom.comp
        (TwoChartIntegralModel.inclInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)).toRingHom :=
    RingHom.ext fun _ => rfl
  have h2 : (chartAlgFin p Γ hj).val.toRingHom =
      (TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)).val.toRingHom.comp
        (TwoChartIntegralModel.inclFin (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)).toRingHom :=
    RingHom.ext fun _ => rfl
  have hg := TwoChartIntegralModel.glue_condition (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)
  rw [h1, h2, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc,
    Category.assoc]
  exact congrArg _ hg

set_option maxHeartbeats 16000000 in
theorem mem_range_ιInf_of_pi
    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iotaInf : ↥(chartAlgInf p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj))
    (iotaInf_spec : ∀ b, (((iotaInf b : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (pi_chartInf : ιInf p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj)
    (z : ↥(X p (ΓM M H) hj)) (hz : π.1 z ∈ Set.range (ιInf p (ΓN p M H hpM) hj)) :
    z ∈ Set.range (ιInf p (ΓM M H) hj) := by
  rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) z with ⟨w, rfl⟩ | h
  swap
  · exact h

  let A : Type := ↥(chartAlgFin p (ΓM M H) hj)
  let 𝔭 : Ideal A := (w : PrimeSpectrum A).asIdeal
  let L : Type := Localization.AtPrime 𝔭
  let g : Spec (CommRingCat.of L) ⟶ TwoChartIntegralModel.XFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) :=
    Spec.map (CommRingCat.ofHom (algebraMap A L))
  have hg : g (IsLocalRing.closedPoint L) = w := by
    apply PrimeSpectrum.ext
    exact Localization.AtPrime.under_maximalIdeal (I := 𝔭)

  have hrange : Set.range (g ≫ ιFin p (ΓM M H) hj ≫ π.1) ⊆ Set.range (ιInf p (ΓN p M H hpM) hj) := by
    refine range_subset_of_isOpen _ (ιInf p (ΓN p M H hpM) hj).isOpenEmbedding.isOpen_range ?_
    simpa only [Scheme.Hom.comp_apply, hg] using hz
  let φ : Spec (CommRingCat.of L) ⟶ TwoChartIntegralModel.XInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) :=
    IsOpenImmersion.lift (ιInf p (ΓN p M H hpM) hj) (g ≫ ιFin p (ΓM M H) hj ≫ π.1) hrange
  have hφ : φ ≫ ιInf p (ΓN p M H hpM) hj = g ≫ ιFin p (ΓM M H) hj ≫ π.1 := IsOpenImmersion.lift_fac _ _ _
  let ψ : ↥(chartAlgInf p (ΓN p M H hpM) hj) →+* L := (Spec.preimage φ).hom
  have hψ : Spec.map (CommRingCat.ofHom ψ) = φ := by
    rw [CommRingCat.ofHom_hom]; exact Spec.map_preimage φ

  have hunit : ∀ s : 𝔭.primeCompl, IsUnit ((chartAlgFin p (ΓM M H) hj).val.toRingHom s) := by
    intro s
    refine isUnit_iff_ne_zero.mpr fun h0 => s.2 ?_
    have : (s : A) = 0 := by
      apply Subtype.ext
      exact h0
    rw [this]; exact zero_mem _
  let v : L →+* ↥(qExpFunctionFieldC ℚ (ΓM M H)) := IsLocalization.lift (M := 𝔭.primeCompl) hunit
  have hv_alg : ∀ a : A, v (algebraMap A L a) = (chartAlgFin p (ΓM M H) hj).val.toRingHom a :=
    fun a => IsLocalization.lift_eq hunit a
  have hvA : v.comp (algebraMap A L) = (chartAlgFin p (ΓM M H) hj).val.toRingHom := RingHom.ext hv_alg
  have hv_inj : Function.Injective v := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists 𝔭.primeCompl L).mp h
      have hc0 : (c : A) ≠ 0 := fun h0 => c.2 (by rw [h0]; exact zero_mem _)
      rw [mul_left_cancel₀ hc0 hc]
    · intro h
      have : x = y := Subtype.ext h
      rw [this]

  have hkey : v.comp ψ = (chartAlgInf p (ΓM M H) hj).val.toRingHom.comp iotaInf.toRingHom := by
    have h1 : Spec.map (CommRingCat.ofHom (v.comp ψ)) ≫ ιInf p (ΓN p M H hpM) hj =
        Spec.map (CommRingCat.ofHom ((chartAlgInf p (ΓM M H) hj).val.toRingHom.comp iotaInf.toRingHom)) ≫
          ιInf p (ΓN p M H hpM) hj := by
      calc Spec.map (CommRingCat.ofHom (v.comp ψ)) ≫ ιInf p (ΓN p M H hpM) hj
          = Spec.map (CommRingCat.ofHom v) ≫ φ ≫ ιInf p (ΓN p M H hpM) hj := by
            rw [← hψ, ← Category.assoc, ← Spec.map_comp]; rfl
        _ = (Spec.map (CommRingCat.ofHom v) ≫ g) ≫ ιFin p (ΓM M H) hj ≫ π.1 := by rw [hφ, Category.assoc]
        _ = Spec.map (CommRingCat.ofHom (chartAlgFin p (ΓM M H) hj).val.toRingHom) ≫ ιFin p (ΓM M H) hj ≫ π.1 := by
            rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hvA]
        _ = Spec.map (CommRingCat.ofHom (chartAlgInf p (ΓM M H) hj).val.toRingHom) ≫ ιInf p (ΓM M H) hj ≫ π.1 := by
            rw [← Category.assoc, specMap_val_ιFin, Category.assoc]
        _ = Spec.map (CommRingCat.ofHom (chartAlgInf p (ΓM M H) hj).val.toRingHom) ≫
              Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj := by rw [pi_chartInf]
        _ = Spec.map (CommRingCat.ofHom ((chartAlgInf p (ΓM M H) hj).val.toRingHom.comp iotaInf.toRingHom)) ≫
              ιInf p (ΓN p M H hpM) hj := by
            rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have h2 := (cancel_mono (ιInf p (ΓN p M H hpM) hj)).mp h1
    rw [Spec.map_inj] at h2
    exact congrArg CommRingCat.Hom.hom h2

  have hvj : v (ψ (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj))) =
      ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))))⁻¹ := by
    have h := RingHom.congr_fun hkey (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj))
    change v (ψ _) = ((iotaInf (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) :
      ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) at h
    rw [h, iotaInf_jInvChartInf iotaInf iotaInf_spec, TwoChartIntegralModel.coe_jInvChartInf]
  have hprod : v (ψ (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) *
      algebraMap A L (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))) = v 1 := by
    rw [map_mul, map_one, hv_alg, hvj]
    change ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))))⁻¹ * ((TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) : A) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = 1
    rw [TwoChartIntegralModel.coe_jChartFin]
    exact inv_mul_cancel₀ (Fact.out : (jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ≠ 0)
  have hU : IsUnit (algebraMap A L (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))) :=
    IsUnit.of_mul_eq_one_right _ (hv_inj hprod)
  have hnot : TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ∉ 𝔭 :=
    (IsLocalization.AtPrime.isUnit_to_map_iff L 𝔭 _).mp hU

  have hw : w ∈ Set.range (TwoChartIntegralModel.fFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) := by
    letI := (TwoChartIntegralModel.inclFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)).toRingHom.toAlgebra
    haveI := TwoChartIntegralModel.isLocalization_away_inclFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
    have hr := PrimeSpectrum.localization_away_comap_range (R := A)
      ↥(TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))
      (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))
    have hmem : (w : PrimeSpectrum A) ∈ (PrimeSpectrum.basicOpen
        (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) : Set (PrimeSpectrum A)) := hnot
    rw [← hr] at hmem
    obtain ⟨w', hw'⟩ := hmem
    exact ⟨w', hw'⟩
  obtain ⟨w', rfl⟩ := hw
  refine ⟨TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) w', ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, TwoChartIntegralModel.glue_condition]

end Key

end RetractInfH

open RetractInfH in
set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iotaInf : ↥(chartAlgInf p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj))
    (iotaInf_spec : ∀ b, (((iotaInf b : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (pi_chartInf : ιInf p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj)

    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (R p) κ]

    (c₀ : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj))) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))).toRingHom) ≫ ιInf p (ΓN p M H hpM) hj)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj)))))
    (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶ fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj)))))

    (comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ) ⟶ fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ)))
    (comp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (comp_isClosedImmersion : ∀ i, IsClosedImmersion (comp i))
    (comp_pi : comp 0 ≫ fibreMap π (algebraMap (R p) κ) = 𝟙 _) :
    ∃ σ₀ : κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj),
      (∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iotaInf z) = z) ∧
      c₀ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c  := by

  haveI hcO : IsOpenImmersion c := isOpenImmersion_chart p (ΓM M H) hj κ c hcfst hcsnd
  haveI hc₀O : IsOpenImmersion c₀ := isOpenImmersion_chart p (ΓN p M H hpM) hj κ c₀ hc₀fst hc₀snd

  have hfm : fibreMap π (algebraMap (R p) κ) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π.1 := by
    rw [fibreMap, pullback.lift_fst]
  have hfm2 : fibreMap (Γ := ΓM M H) (Γ' := ΓN p M H hpM) (hj := hj) π (algebraMap (R p) κ) ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
    rw [fibreMap, pullback.lift_snd, Category.comp_id]
  have hS : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iotaInf).toRingHom) ≫ c₀ =
      c ≫ fibreMap π (algebraMap (R p) κ) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hc₀fst, Category.assoc, hfm, reassoc_of% hcfst, pi_chartInf, ← Spec.map_comp_assoc,
        ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 3
    · rw [Category.assoc, hc₀snd, Category.assoc, hfm2, hcsnd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      all_goals exact RingHom.ext fun a => by simp

  have hrange : Set.range (c₀ ≫ comp 0) ⊆ Set.range c := by
    rintro _ ⟨y, rfl⟩
    apply mem_range_chart p (ΓM M H) hj κ c hcfst hcsnd
    apply mem_range_ιInf_of_pi π iotaInf iotaInf_spec pi_chartInf
    have hm : (c₀ ≫ comp 0) ≫ pullback.fst _ _ ≫ π.1 =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))).toRingHom) ≫ ιInf p (ΓN p M H hpM) hj := by
      rw [← hfm, Category.assoc, reassoc_of% comp_pi]
      rw [hc₀fst]
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

  let ℓ := IsOpenImmersion.lift c (c₀ ≫ comp 0) hrange
  have hℓ : ℓ ≫ c = c₀ ≫ comp 0 := IsOpenImmersion.lift_fac _ _ _
  let τ : κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →+* κ ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj) := (Spec.preimage ℓ).hom
  have hτ : Spec.map (CommRingCat.ofHom τ) = ℓ := by
    rw [CommRingCat.ofHom_hom]; exact Spec.map_preimage ℓ

  have hτleft : τ.comp Algebra.TensorProduct.includeLeftRingHom = Algebra.TensorProduct.includeLeftRingHom := by
    have h1 : Spec.map (CommRingCat.ofHom (τ.comp Algebra.TensorProduct.includeLeftRingHom)) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj)))) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hτ, ← hcsnd, reassoc_of% hℓ, comp_over 0, hc₀snd]
    rw [Spec.map_inj] at h1
    exact congrArg CommRingCat.Hom.hom h1
  let σ₀ : κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj) :=
    { τ with
      commutes' := fun r => by
        have := RingHom.congr_fun hτleft r
        simpa [Algebra.TensorProduct.algebraMap_apply] using this }
  have hσ₀ : σ₀.toRingHom = τ := rfl
  refine ⟨σ₀, ?_, ?_⟩
  ·
    have h3 : (Spec.map (CommRingCat.ofHom τ) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iotaInf).toRingHom)) ≫ c₀ = 𝟙 _ ≫ c₀ := by
      rw [Category.assoc, hS, hτ, reassoc_of% hℓ, comp_pi, Category.comp_id, Category.id_comp]
    have h4 := (cancel_mono c₀).mp h3
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id, ← CommRingCat.ofHom_id, Spec.map_inj] at h4
    have h5 := congrArg CommRingCat.Hom.hom h4
    intro z
    exact RingHom.congr_fun h5 z
  · change c₀ ≫ comp 0 = Spec.map (CommRingCat.ofHom τ) ≫ c
    rw [hτ, hℓ]

end S_ModularCurve_XHDRLevel_exists_retraction_chartInf_comp_zero_eq_of_dvd
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_retraction_chartInf_comp_zero_eq_of_dvd (solution)

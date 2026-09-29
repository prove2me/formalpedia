-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.isFinite_flat_finrank_curveChange_heckeDegeneracy_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/615a2f72-aaf1-5a77-9d2e-0b75ed3b3447

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

import Theorems.Thm_ModularCurve_isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charZero
import Theorems.Thm_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_morphismRestrict_eq_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_curveChange_heckeDegeneracy_rat
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra ModularCurve ModularCurve.XHDRLevel CongruenceSubgroup

open scoped MatrixGroups

namespace E1Aux

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem exists_mul_pow_mem (p : ℕ) (hp : p.Prime) (q : ℚ) :
    ∃ (n : ℕ) (a : ℚ), a ∈ GaloisRep.ratLocalizedAt p ∧ q * (p : ℚ) ^ n = a := by
  obtain ⟨n, d, hd, hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp.ne_one
  refine ⟨n, q * (p : ℚ) ^ n, ?_, rfl⟩
  show (q * (p : ℚ) ^ n).den.Coprime p
  have hq : q * (p : ℚ) ^ n = (q.num : ℚ) / (d : ℚ) := by
    have hdq : (q.den : ℚ) = (p : ℚ) ^ n * (d : ℚ) := by exact_mod_cast hden
    have hd0 : (d : ℚ) ≠ 0 := by
      intro h
      have : q.den = 0 := by exact_mod_cast (show (q.den : ℚ) = 0 by rw [hdq, h, mul_zero])
      exact q.den_nz this
    rw [eq_div_iff hd0]
    calc q * (p : ℚ) ^ n * (d : ℚ) = q * (q.den : ℚ) := by rw [hdq]; ring
      _ = (q.num : ℚ) := Rat.mul_den_eq_num q
  rw [hq]
  have hdvd : ((q.num : ℚ) / (d : ℚ)).den ∣ d := by
    have h1 : (((q.num : ℚ) / (d : ℚ)).den : ℤ) ∣ (d : ℤ) := by
      have := Rat.den_dvd q.num d
      simpa [Rat.divInt_eq_div] using this
    exact Int.natCast_dvd_natCast.mp h1
  exact Nat.Coprime.coprime_dvd_left hdvd ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd).symm

scoped instance isLocalizationAway (p : ℕ) [Fact p.Prime] :
    IsLocalization.Away ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ℚ where
  map_units := by
    rintro ⟨_, n, rfl⟩
    simp only [map_pow]
    exact IsUnit.pow _ (by
      rw [isUnit_iff_ne_zero, map_natCast]
      exact_mod_cast (Fact.out : p.Prime).ne_zero)
  surj := fun q => by
    obtain ⟨n, a, ha, hqa⟩ := exists_mul_pow_mem p Fact.out q
    exact ⟨⟨⟨a, ha⟩, ⟨_, n, rfl⟩⟩, by simp at hqa ⊢; exact hqa⟩
  exists_of_eq := fun {x y} h => ⟨1, by
    have : (x : ℚ) = y := h
    simpa using Subtype.ext this⟩

theorem ringKrullDim_le_one {A : Type*} [CommRing A] [IsDomain A] [Ring.DimensionLEOne A] :
    ringKrullDim A ≤ 1 := by
  rw [ringKrullDim, Order.krullDim_le_one_iff]
  intro P
  by_cases hP : P.asIdeal = ⊥
  · left
    intro Q hQ
    exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp (hP ▸ bot_le)
  · right
    intro Q hQ
    have hmax := Ring.DimensionLEOne.maximalOfPrime hP P.isPrime
    exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp (hmax.eq_of_le Q.isPrime.ne_top hQ).ge

end E1Aux
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_curveChange_heckeDegeneracy_rat.E1Aux"

set_option maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (πα πβ : SchemeHomOver (toBase p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj) (toBase p (ΓM M H) hj))
    [IsFinite πα.1] [IsFinite πβ.1] [LocallyOfFinitePresentation πα.1] [LocallyOfFinitePresentation πβ.1]
    (U : (X p (ΓM M H) hj).Opens)
    (hU : ∀ x : ↥(X p (ΓM M H) hj), ringKrullDim ((X p (ΓM M H) hj).presheaf.stalk x) ≤ 1 → x ∈ U)
    [Flat (πα.1 ∣_ U)] [Flat (πβ.1 ∣_ U)]
    (hrkα : ∀ y : ↥(X p (ΓM M H) hj), y ∈ U → πα.1.finrank y = (if ℓ ∣ M then ℓ else ℓ + 1))
    (hrkβ : ∀ y : ↥(X p (ΓM M H) hj), y ∈ U → πβ.1.finrank y = (if ℓ ∣ M then ℓ else ℓ + 1)) :
    ∃ (_ : IsFinite (RelPicard.curveChange πα.1 πα.2 (SmoothProperCurve.specMap (R p) ℚ)))
      (_ : IsFinite (RelPicard.curveChange πβ.1 πβ.2 (SmoothProperCurve.specMap (R p) ℚ)))
      (_ : LocallyOfFinitePresentation (RelPicard.curveChange πα.1 πα.2 (SmoothProperCurve.specMap (R p) ℚ)))
      (_ : LocallyOfFinitePresentation (RelPicard.curveChange πβ.1 πβ.2 (SmoothProperCurve.specMap (R p) ℚ))),
      Flat (RelPicard.curveChange πα.1 πα.2 (SmoothProperCurve.specMap (R p) ℚ)) ∧
      Flat (RelPicard.curveChange πβ.1 πβ.2 (SmoothProperCurve.specMap (R p) ℚ)) ∧
      (∀ y, (RelPicard.curveChange πα.1 πα.2 (SmoothProperCurve.specMap (R p) ℚ)).finrank y = (if ℓ ∣ M then ℓ else ℓ + 1)) ∧
      (∀ y, (RelPicard.curveChange πβ.1 πβ.2 (SmoothProperCurve.specMap (R p) ℚ)).finrank y = (if ℓ ∣ M then ℓ else ℓ + 1)) := by
  classical
  let t := SmoothProperCurve.specMap (R p) ℚ

  have hsq : ∀ (π : SchemeHomOver (toBase p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj) (toBase p (ΓM M H) hj)),
      IsPullback (pullback.fst (toBase p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj) t) (RelPicard.curveChange π.1 π.2 t) π.1
        (pullback.fst (toBase p (ΓM M H) hj) t) := by
    intro π
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback (toBase p (ΓM M H) hj) t)
    · have h1 : RelPicard.curveChange π.1 π.2 t ≫ pullback.snd (toBase p (ΓM M H) hj) t =
          pullback.snd (toBase p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj) t := by
        simp only [RelPicard.curveChange, pullback.map, pullback.lift_snd, Category.comp_id]
      rw [h1, π.2]
      exact IsPullback.of_hasPullback _ _
    · simp only [RelPicard.curveChange, pullback.map, pullback.lift_fst]

  haveI hfinα : IsFinite (RelPicard.curveChange πα.1 πα.2 t) := MorphismProperty.of_isPullback (hsq πα) inferInstance
  haveI hfinβ : IsFinite (RelPicard.curveChange πβ.1 πβ.2 t) := MorphismProperty.of_isPullback (hsq πβ) inferInstance
  haveI hlfpα : LocallyOfFinitePresentation (RelPicard.curveChange πα.1 πα.2 t) :=
    MorphismProperty.of_isPullback (hsq πα) inferInstance
  haveI hlfpβ : LocallyOfFinitePresentation (RelPicard.curveChange πβ.1 πβ.2 t) :=
    MorphismProperty.of_isPullback (hsq πβ) inferInstance

  haveI : IsOpenImmersion t := IsOpenImmersion.of_isLocalization ((p : ℕ) : R p)
  have hmem : ∀ z : ↥(pullback (toBase p (ΓM M H) hj) t), (pullback.fst (toBase p (ΓM M H) hj) t).base z ∈ U := by
    intro z
    apply hU
    have e := (asIso ((pullback.fst (toBase p (ΓM M H) hj) t).stalkMap z)).commRingCatIsoToRingEquiv
    rw [RingEquiv.ringKrullDim e]
    haveI : IsIntegral ↑(pullback (toBase p (ΓM M H) hj) t) :=
      ModularCurve.isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charZero (ΓM M H) p (jAt (ΓM M H) hj) ℚ
    haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓM M H) hj) t) := 𝔛.smooth_generic
    haveI : ValuationRing ((pullback (toBase p (ΓM M H) hj) t).presheaf.stalk z) :=
      AlgebraicGeometry.valuationRing_stalk_of_smoothOfRelativeDimension_one (pullback.snd (toBase p (ΓM M H) hj) t) z
    haveI : IsLocallyNoetherian (pullback (toBase p (ΓM M H) hj) t) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (toBase p (ΓM M H) hj) t)
    exact E1Aux.ringKrullDim_le_one

  have hrest : ∀ (π : SchemeHomOver (toBase p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj) (toBase p (ΓM M H) hj)) (d : ℕ),
      IsFinite π.1 → Flat (π.1 ∣_ U) → (∀ y : ↥(X p (ΓM M H) hj), y ∈ U → π.1.finrank y = d) →
      Flat (RelPicard.curveChange π.1 π.2 t) ∧ ∀ y, (RelPicard.curveChange π.1 π.2 t).finrank y = d := by
    intro π d hfin hflatU hrk
    haveI := hflatU
    haveI := hfin
    haveI : IsFinite (π.1 ∣_ U) := MorphismProperty.of_isPullback (isPullback_morphismRestrict π.1 U).flip hfin

    have hrange : Set.range (pullback.fst (toBase p (ΓM M H) hj) t).base ⊆ Set.range U.ι.base := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hmem z
    let fU := IsOpenImmersion.lift U.ι (pullback.fst (toBase p (ΓM M H) hj) t) hrange
    have hfU : fU ≫ U.ι = pullback.fst (toBase p (ΓM M H) hj) t := IsOpenImmersion.lift_fac _ _ _
    have hrange' : Set.range (pullback.fst (toBase p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj) t).base ⊆ Set.range (π.1 ⁻¹ᵁ U).ι.base := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (pullback.fst (toBase p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj) t ≫ π.1).base z ∈ U
      rw [(hsq π).w]
      exact hmem _
    let fU' := IsOpenImmersion.lift (π.1 ⁻¹ᵁ U).ι (pullback.fst (toBase p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj) t) hrange'
    have hfU' : fU' ≫ (π.1 ⁻¹ᵁ U).ι = pullback.fst (toBase p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj) t := IsOpenImmersion.lift_fac _ _ _

    have sq : IsPullback fU' (RelPicard.curveChange π.1 π.2 t) (π.1 ∣_ U) fU := by
      refine IsPullback.of_right (h₁₂ := (π.1 ⁻¹ᵁ U).ι) (h₂₂ := U.ι) ?_ ?_ (isPullback_morphismRestrict π.1 U).flip
      · rw [hfU', hfU]
        exact hsq π
      · rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι, hfU, ← Category.assoc, hfU']
        exact (hsq π).w
    refine ⟨MorphismProperty.of_isPullback sq inferInstance, fun y => ?_⟩
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq y]
    have hyU : (pullback.fst (toBase p (ΓM M H) hj) t).base y ∈ U := hmem y
    have hpt : fU.base y = ⟨(pullback.fst (toBase p (ΓM M H) hj) t).base y, hyU⟩ := by
      apply Subtype.ext
      show (fU ≫ U.ι).base y = _
      rw [hfU]
    rw [hpt, AlgebraicGeometry.Scheme.Hom.finrank_morphismRestrict_eq_finrank π.1 U _ hyU]
    exact hrk _ hyU
  obtain ⟨hflα, hdα⟩ := hrest πα _ inferInstance inferInstance hrkα
  obtain ⟨hflβ, hdβ⟩ := hrest πβ _ inferInstance inferInstance hrkβ
  exact ⟨hfinα, hfinβ, hlfpα, hlfpβ, hflα, hflβ, hdα, hdβ⟩

#print axioms solution

end S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_curveChange_heckeDegeneracy_rat
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_curveChange_heckeDegeneracy_rat (solution)

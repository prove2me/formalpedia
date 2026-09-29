-- Prove2me | solution 1 for ModularCurve.XOneP.exists_valuationSubring_ringEquiv_stalk_of_ringKrullDim_le_one_twoChartIntegralModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/27eca830-cb99-5d7c-a44a-de944789f175

import Mathlib
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_valuationSubring_eq_of_isPrime_span_of_forall_aeval_mem
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_valuationSubring_ringEquiv_stalk_of_ringKrullDim_le_one_twoChartIntegralModel_x1_mul
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

universe u

open scoped TensorProduct

namespace CBCore
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem exists_stalk_iso_localization_chartAlgFin
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (y : ↥(XFin R F j)) (hxy : (ιFin R F j).base y = x) :
    ∃ (e : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x ≅
        CommRingCat.of (Localization.AtPrime y.asIdeal)),
      (∀ r : R, e.hom (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ x trivial).hom
          (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))
        = algebraMap ↥(chartAlgFin R F j) (Localization.AtPrime y.asIdeal) (algebraMap R ↥(chartAlgFin R F j) r)) ∧
      (∀ a : ↥(chartAlgFin R F j), ∀ s : Localization.AtPrime y.asIdeal,
          s = algebraMap ↥(chartAlgFin R F j) (Localization.AtPrime y.asIdeal) a →
          ∃ t, e.hom t = s) := by
  subst hxy
  haveI : IsIso ((ιFin R F j).stalkMap y) := inferInstance
  let e : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y) ≅
      CommRingCat.of (Localization.AtPrime y.asIdeal) :=
    asIso ((ιFin R F j).stalkMap y) ≪≫ Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F j)) y
  refine ⟨e, fun r => ?_, fun a s hs => ⟨e.inv s, by simp⟩⟩

  change (Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F j)) y).hom.hom
      (((ιFin R F j).stalkMap y).hom (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιFin R F j).base y) trivial).hom
        (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) = _
  rw [Scheme.Hom.germ_stalkMap_apply (ιFin R F j) ⊤ y trivial]

  have h1 : ((ιFin R F j).app ⊤).hom (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      ((Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j)))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    change (((toBase R F j).appTop ≫ (ιFin R F j).appTop)).hom _ = _
    rw [← Scheme.Hom.comp_appTop, ιFin_toBase]
  have h2 : ((Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j)))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom (algebraMap R ↥(chartAlgFin R F j) r) := by
    have hn := congrArg (fun φ : CommRingCat.of R ⟶ _ => φ.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
    exact hn.symm
  rw [h1, h2]

  have h3 := congrArg (fun φ : CommRingCat.of ↥(chartAlgFin R F j) ⟶ _ => φ.hom (algebraMap R ↥(chartAlgFin R F j) r))
    (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of ↥(chartAlgFin R F j)) y)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3

  first
    | rw [← h3]
    | erw [← h3]
  change ((Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F j)) y).inv ≫ (Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F j)) y).hom).hom _ = _
  rw [Iso.inv_hom_id]
  rfl

theorem exists_stalk_iso_localization_chartAlgInf
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (y : ↥(XInf R F j)) (hxy : (ιInf R F j).base y = x) :
    ∃ (e : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x ≅
        CommRingCat.of (Localization.AtPrime y.asIdeal)),
      (∀ r : R, e.hom (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ x trivial).hom
          (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))
        = algebraMap ↥(chartAlgInf R F j) (Localization.AtPrime y.asIdeal) (algebraMap R ↥(chartAlgInf R F j) r)) ∧
      (∀ a : ↥(chartAlgInf R F j), ∀ s : Localization.AtPrime y.asIdeal,
          s = algebraMap ↥(chartAlgInf R F j) (Localization.AtPrime y.asIdeal) a →
          ∃ t, e.hom t = s) := by
  subst hxy
  haveI : IsIso ((ιInf R F j).stalkMap y) := inferInstance
  let e : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιInf R F j).base y) ≅
      CommRingCat.of (Localization.AtPrime y.asIdeal) :=
    asIso ((ιInf R F j).stalkMap y) ≪≫ Spec.stalkIso (CommRingCat.of ↥(chartAlgInf R F j)) y
  refine ⟨e, fun r => ?_, fun a s hs => ⟨e.inv s, by simp⟩⟩

  change (Spec.stalkIso (CommRingCat.of ↥(chartAlgInf R F j)) y).hom.hom
      (((ιInf R F j).stalkMap y).hom (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιInf R F j).base y) trivial).hom
        (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) = _
  rw [Scheme.Hom.germ_stalkMap_apply (ιInf R F j) ⊤ y trivial]

  have h1 : ((ιInf R F j).app ⊤).hom (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      ((Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgInf R F j)))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    change (((toBase R F j).appTop ≫ (ιInf R F j).appTop)).hom _ = _
    rw [← Scheme.Hom.comp_appTop, ιInf_toBase]
  have h2 : ((Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgInf R F j)))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom (algebraMap R ↥(chartAlgInf R F j) r) := by
    have hn := congrArg (fun φ : CommRingCat.of R ⟶ _ => φ.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R ↥(chartAlgInf R F j))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
    exact hn.symm
  rw [h1, h2]

  have h3 := congrArg (fun φ : CommRingCat.of ↥(chartAlgInf R F j) ⟶ _ => φ.hom (algebraMap R ↥(chartAlgInf R F j) r))
    (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of ↥(chartAlgInf R F j)) y)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3

  first
    | rw [← h3]
    | erw [← h3]
  change ((Spec.stalkIso (CommRingCat.of ↥(chartAlgInf R F j)) y).inv ≫ (Spec.stalkIso (CommRingCat.of ↥(chartAlgInf R F j)) y).hom).hom _ = _
  rw [Iso.inv_hom_id]
  rfl

theorem mem_asIdeal_and_ringKrullDim_localization_le_one_of_ιInf
    (ϖ : R) (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (y : ↥(XInf R F j)) (hxy : (ιInf R F j).base y = x)
    (hz : ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ x trivial).hom
        (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)) ∈
      IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x))
    (hdim : ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x) ≤ 1) :
    algebraMap R ↥(chartAlgInf R F j) ϖ ∈ y.asIdeal ∧ ringKrullDim (Localization.AtPrime y.asIdeal) ≤ 1 := by
  obtain ⟨e, he, -⟩ := exists_stalk_iso_localization_chartAlgInf R F j x y hxy
  refine ⟨?_, ?_⟩
  ·
    have hnu : ¬ IsUnit (e.hom.hom (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ x trivial).hom
        (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)))) := by
      intro hu
      apply (IsLocalRing.mem_maximalIdeal _).mp hz
      exact (isUnit_map_iff e.commRingCatIsoToRingEquiv _).mp hu
    rw [he] at hnu
    have hmax : algebraMap ↥(chartAlgInf R F j) (Localization.AtPrime y.asIdeal) (algebraMap R ↥(chartAlgInf R F j) ϖ) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime y.asIdeal) := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime y.asIdeal) y.asIdeal _).mp hmax
  · rw [← ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv]
    exact hdim

theorem exists_ιFin_base_eq_ιInf_base_of_jInvChartInf_not_mem
    (y : ↥(XInf R F j)) (hy : (jInvChartInf R F j : ↥(chartAlgInf R F j)) ∉ y.asIdeal) :
    ∃ y' : ↥(XFin R F j), (ιFin R F j).base y' = (ιInf R F j).base y := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j

  have hmem : y ∈ Set.range (PrimeSpectrum.comap (algebraMap ↥(chartAlgInf R F j) ↥(chartAlgMid R F j))) := by
    rw [PrimeSpectrum.localization_away_comap_range ↥(chartAlgMid R F j) (jInvChartInf R F j)]
    exact hy
  obtain ⟨w, hw⟩ := hmem
  refine ⟨(fFin R F j).base w, ?_⟩
  have hglue := congrArg (fun φ => φ.base w) (glue_condition R F j)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hglue
  rw [hglue]
  exact congrArg (fun t => (ιInf R F j).base t) hw

theorem mem_minimalPrimes_span_of_ringKrullDim_le_one {C : Type u} [CommRing C] [IsDomain C]
    (𝔭 : Ideal C) [𝔭.IsPrime] (ϖ : C) (hϖ : ϖ ∈ 𝔭) (hϖ0 : ϖ ≠ 0)
    (hdim : ringKrullDim (Localization.AtPrime 𝔭) ≤ 1) :
    𝔭 ∈ (Ideal.span {ϖ}).minimalPrimes := by
  have hh : 𝔭.height ≤ (1 : ℕ) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 (Localization.AtPrime 𝔭)] at hdim
    exact_mod_cast hdim
  refine ⟨⟨‹𝔭.IsPrime›, (Ideal.span_singleton_le_iff_mem _).mpr hϖ⟩, ?_⟩
  rintro q ⟨hq, hϖq⟩ hle
  by_contra hne
  have hlt : q < 𝔭 := lt_of_le_of_ne hle (fun h => hne (h ▸ le_rfl))
  have hq0 : q.height < (1 : ℕ) := (Ideal.height_le_iff.mp hh) q hq hlt
  have hq00 : q.height = 0 := by
    have : q.height < 1 := by exact_mod_cast hq0
    exact ENat.lt_one_iff_eq_zero.mp this

  have hqbot : q = ⊥ := by
    have hmin : q ∈ minimalPrimes C := Ideal.height_eq_zero_iff.mp hq00
    exact le_bot_iff.mp (hmin.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le)
  exact hϖ0 (by simpa [hqbot] using (Ideal.span_singleton_le_iff_mem _).mp hϖq)

theorem jInvChartInf_not_mem_of_mem_minimalPrimes
    [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (𝔓 : Ideal ↥(chartAlgInf R F j))
    (h𝔓 : 𝔓 ∈ (Ideal.span {algebraMap R ↥(chartAlgInf R F j) ϖ}).minimalPrimes) :
    jInvChartInf R F j ∉ 𝔓 := by
  haveI : Fact (j⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : j ≠ 0)⟩
  have htj' : Transcendental R j⁻¹ := fun h => htj (IsAlgebraic.inv_iff.mp h)
  have hadj : IntermediateField.adjoin K₀ ({j⁻¹} : Set F) = IntermediateField.adjoin K₀ ({j} : Set F) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self K₀ j)
    · rw [IntermediateField.adjoin_simple_le_iff]
      simpa using inv_mem (IntermediateField.mem_adjoin_simple_self K₀ j⁻¹)
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := by rw [hadj]; exact hFD
  have hsep' : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := by rw [hadj]; exact hsep
  obtain ⟨V, -, -, hcentre, -, hunits⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
      R K₀ F j⁻¹ htj' hFD' hsep' ϖ hϖ 𝔓 h𝔓
  have hX : ¬ (Polynomial.C ϖ ∣ (Polynomial.X : Polynomial R)) := by
    rintro ⟨Q, hQ⟩
    have h1 : (Polynomial.X : Polynomial R).coeff 1 = ϖ * Q.coeff 1 := by rw [hQ, Polynomial.coeff_C_mul]
    rw [Polynomial.coeff_X_one] at h1
    exact hϖ.not_unit (isUnit_of_dvd_one ⟨_, h1⟩)
  obtain ⟨hjV, hjiV⟩ := hunits Polynomial.X hX
  rw [Polynomial.aeval_X] at hjV hjiV
  rw [inv_inv] at hjiV
  intro hmem
  have hnu : ((jInvChartInf R F j : ↥(chartAlgInf R F j)) : F) ∈ V.nonunits := (hcentre _).mp hmem
  rw [ValuationSubring.mem_nonunits_iff] at hnu
  have hle : V.valuation j ≤ 1 := (V.valuation_le_one_iff _).mpr hjiV
  have hlt : V.valuation (((jInvChartInf R F j : ↥(chartAlgInf R F j)) : F) * j) < 1 := by
    rw [map_mul]
    calc V.valuation ((jInvChartInf R F j : ↥(chartAlgInf R F j)) : F) * V.valuation j
        ≤ V.valuation ((jInvChartInf R F j : ↥(chartAlgInf R F j)) : F) * 1 := mul_le_mul_right hle _
      _ < 1 := by rw [mul_one]; exact hnu
  have hone : (((jInvChartInf R F j : ↥(chartAlgInf R F j)) : F) * j) = 1 := by
    rw [coe_jInvChartInf, inv_mul_cancel₀ (Fact.out : j ≠ 0)]
  rw [hone, map_one] at hlt
  exact lt_irrefl _ hlt

theorem exists_ιFin_base_eq_of_germ_mem_maximalIdeal_of_ringKrullDim_le_one
    [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (hx : ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ x trivial).hom
        (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))
      ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x))
    (hdim : ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x) ≤ 1) :
    ∃ y : ↥(XFin R F j), (ιFin R F j).base y = x := by
  rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact ⟨y, hy⟩
  ·
    obtain ⟨hmem, hdim'⟩ := mem_asIdeal_and_ringKrullDim_localization_le_one_of_ιInf R F j ϖ x y hy hx hdim
    have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
    have hϖp : Prime ϖ := hϖirr.prime
    have hϖ0 : algebraMap R ↥(chartAlgInf R F j) ϖ ≠ 0 := by
      intro h
      apply hϖp.ne_zero
      have hinj : Function.Injective (algebraMap R ↥(chartAlgInf R F j)) := by
        intro a b hab
        have h' : algebraMap R F a = algebraMap R F b := by
          simpa [Subalgebra.coe_algebraMap] using congrArg (fun c : ↥(chartAlgInf R F j) => (c : F)) hab
        rw [IsScalarTower.algebraMap_eq R K₀ F] at h'
        exact IsFractionRing.injective R K₀ ((algebraMap K₀ F).injective h')
      exact hinj (h.trans (map_zero _).symm)
    haveI : y.asIdeal.IsPrime := y.isPrime
    have hmin := mem_minimalPrimes_span_of_ringKrullDim_le_one y.asIdeal _ hmem hϖ0 hdim'
    have hnot := jInvChartInf_not_mem_of_mem_minimalPrimes R F j K₀ htj hFD hsep ϖ hϖp y.asIdeal hmin
    obtain ⟨y', hy'⟩ := exists_ιFin_base_eq_ιInf_base_of_jInvChartInf_not_mem R F j y hnot
    exact ⟨y', hy'.trans hy⟩

theorem exists_ringEquiv_localization_of_forall_mem_iff
    {C : Type u} [CommRing C] [IsDomain C] [Algebra C F] [FaithfulSMul C F]
    (𝔭 : Ideal C) [𝔭.IsPrime] (V : ValuationSubring F)
    (hCV : ∀ a : C, algebraMap C F a ∈ V)
    (hV : ∀ f : F, f ∈ V ↔ ∃ a b : C, b ∉ 𝔭 ∧ f * algebraMap C F b = algebraMap C F a)
    (hnu : ∀ a : C, algebraMap C F a ∈ V.nonunits ↔ a ∈ 𝔭) :
    ∃ e : Localization.AtPrime 𝔭 ≃+* ↥V,
      ∀ a : C, ((e (algebraMap C (Localization.AtPrime 𝔭) a) : ↥V) : F) = algebraMap C F a := by
  classical
  let g : C →+* ↥V := (algebraMap C F).codRestrict V hCV
  have hg : ∀ a : C, ((g a : ↥V) : F) = algebraMap C F a := fun a => rfl

  have hunit : ∀ b : ↥𝔭.primeCompl, IsUnit (g ↑b) := by
    intro b
    have hb : (b : C) ∉ 𝔭 := b.2
    rw [← hnu, ← hg, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      not_not] at hb
    exact hb
  refine ⟨RingEquiv.ofBijective (IsLocalization.lift (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭) hunit)
    ⟨?_, ?_⟩, fun a => ?_⟩
  · rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      exact congrArg g ((IsLocalization.injective (Localization.AtPrime 𝔭) (Ideal.primeCompl_le_nonZeroDivisors 𝔭)) h)
    · intro h
      have : algebraMap C F x = algebraMap C F y := by rw [← hg, ← hg, h]
      rw [(FaithfulSMul.algebraMap_injective C F) this]
  · rw [IsLocalization.lift_surjective_iff]
    intro v
    obtain ⟨a, b, hb, hab⟩ := (hV (v : F)).mp v.2
    refine ⟨(a, ⟨b, hb⟩), Subtype.ext ?_⟩
    show (v : F) * ((g b : ↥V) : F) = ((g a : ↥V) : F)
    rw [hg, hg, hab]
  · show ((IsLocalization.lift hunit (algebraMap C (Localization.AtPrime 𝔭) a) : ↥V) : F) = _
    rw [IsLocalization.lift_eq]
    rfl

end CBCore

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (hdim : ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≤ 1) :
    ∃ (V : ValuationSubring ↥K) (e : ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+* ↥V),
      (∀ a : A, algebraMap A ↥K a ∈ V) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits) ∧
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) ∧
      ((e ϖz : ↥V) : ↥K) = algebraMap A ↥K ϖ ∧
      (∀ a : A, ((e (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) : ↥V) : ↥K) = algebraMap A ↥K a) := by
  classical

  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK j hj
  haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsIntegral.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hϖp : Prime ϖ := hϖirr.prime

  subst hϖz
  obtain ⟨y, rfl⟩ := CBCore.exists_ιFin_base_eq_of_germ_mem_maximalIdeal_of_ringKrullDim_le_one
    A (↥K) j L htj hFD hsep ϖ hϖ z hz hdim
  obtain ⟨e₁, he₁, -⟩ := CBCore.exists_stalk_iso_localization_chartAlgFin A (↥K) j _ y rfl
  set C := ↥(chartAlgFin A (↥K) j) with hCdef
  set 𝔭 : Ideal C := y.asIdeal with h𝔭def
  let e₁' : ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((ιFin A (↥K) j).base y)) ≃+* Localization.AtPrime 𝔭 :=
    e₁.commRingCatIsoToRingEquiv
  have he₁' : ∀ r : A, e₁' (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ _ trivial).hom
      (((toBase A (↥K) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r)))
      = algebraMap C (Localization.AtPrime 𝔭) (algebraMap A C r) := he₁

  have hϖ𝔭 : algebraMap A C ϖ ∈ 𝔭 := by
    have h1 : e₁' _ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) :=
      (IsLocalRing.mem_maximalIdeal _).mpr ((mem_nonunits_iff).mpr
        (fun hu => ((IsLocalRing.mem_maximalIdeal _).mp hz) ((isUnit_map_iff e₁' _).mp hu)))
    rw [he₁'] at h1
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔭) 𝔭 _).mp h1
  have hϖC0 : algebraMap A C ϖ ≠ 0 := by
    intro h0
    apply hϖp.ne_zero
    have : algebraMap A ↥K ϖ = 0 := by
      rw [IsScalarTower.algebraMap_apply A C ↥K, h0, map_zero]
    rw [IsScalarTower.algebraMap_apply A L ↥K, map_eq_zero] at this
    exact (IsFractionRing.injective A L) (this.trans (map_zero _).symm)
  have hdim' : ringKrullDim (Localization.AtPrime 𝔭) ≤ 1 := by
    rwa [← ringKrullDim_eq_of_ringEquiv e₁']
  have h𝔭min : 𝔭 ∈ (Ideal.span {algebraMap A C ϖ}).minimalPrimes :=
    CBCore.mem_minimalPrimes_span_of_ringKrullDim_le_one 𝔭 _ hϖ𝔭 hϖC0 hdim'

  obtain ⟨V, hVdvr, hAV, hcentre, hϖV, hVj⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
      A L (↥K) j htj hFD hsep ϖ hϖp 𝔭 h𝔭min
  have h1 : ∀ a : A, algebraMap A ↥K a ∈ V := fun a => by
    rw [IsScalarTower.algebraMap_apply A C ↥K]; exact hAV _
  have h2 : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits := by
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul]
    rw [ValuationSubring.mem_nonunits_iff, map_mul]
    have hc : V.valuation (algebraMap A ↥K c) ≤ 1 := V.valuation_le_one ⟨_, h1 c⟩
    have hϖ1 : V.valuation (algebraMap A ↥K ϖ) < 1 := (ValuationSubring.mem_nonunits_iff _).mp hϖV
    calc V.valuation (algebraMap A ↥K ϖ) * V.valuation (algebraMap A ↥K c)
        ≤ V.valuation (algebraMap A ↥K ϖ) * 1 := mul_le_mul_right hc _
      _ < 1 := by rw [mul_one]; exact hϖ1
  have h3 : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V := by
    intro P hP
    refine hVj P (fun hdvd => hP ?_)
    obtain ⟨Q, rfl⟩ := hdvd
    rw [Polynomial.map_mul, Polynomial.map_C]
    have : IsLocalRing.residue A ϖ = 0 :=
      (IsLocalRing.residue_eq_zero_iff ϖ).mpr (hϖ ▸ Ideal.mem_span_singleton_self ϖ)
    rw [this, Polynomial.C_0, zero_mul]
  obtain ⟨-, ⟨𝔓, h𝔓, -, h𝔓V, -, hloc⟩, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      A L (↥K) j htj hFD hsep V h1 h2 h3
  have h𝔓𝔭 : 𝔓 = 𝔭 := by
    ext b; rw [h𝔓V, hcentre]

  obtain ⟨e₂, he₂⟩ := CBCore.exists_ringEquiv_localization_of_forall_mem_iff (F := ↥K) 𝔭 V hAV
    (fun f => by
      rw [hloc]
      constructor
      · rintro ⟨a, b, hb, hab⟩; exact ⟨a, b, h𝔓𝔭 ▸ hb, hab⟩
      · rintro ⟨a, b, hb, hab⟩; exact ⟨a, b, h𝔓𝔭 ▸ hb, hab⟩)
    (fun a => (hcentre a).symm)

  refine ⟨V, e₁'.trans e₂, h1, h2, h3, ?_, ?_⟩
  · show ((e₂ (e₁' _) : ↥V) : ↥K) = _
    rw [he₁', he₂, ← IsScalarTower.algebraMap_apply]
  · intro a
    show ((e₂ (e₁' _) : ↥V) : ↥K) = _
    rw [he₁', he₂, ← IsScalarTower.algebraMap_apply]

end S_ModularCurve_XOneP_exists_valuationSubring_ringEquiv_stalk_of_ringKrullDim_le_one_twoChartIntegralModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_valuationSubring_ringEquiv_stalk_of_ringKrullDim_le_one_twoChartIntegralModel_x1_mul (solution)

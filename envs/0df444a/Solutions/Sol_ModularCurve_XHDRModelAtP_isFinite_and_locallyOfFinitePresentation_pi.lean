-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.isFinite_and_locallyOfFinitePresentation_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/39d4ef24-1001-5c54-a7bd-fe0bdb5e70ab

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi.ModularCurve ModularCurve.XHDRLevel"

open scoped MatrixGroups

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel TwoChartIntegralModel.isOpenImmersion_ιFin TwoChartIntegralModel.isOpenImmersion_ιInf"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlg mem_chartAlg_iff adjoin_le_chartAlg subset_chartAlg chartAlgFin chartAlgInf chartAlgMid jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf inclFin inclInf isLocalization_away_inclFin isLocalization_away_inclInf XFin XInf XMid fFin fInf ιFin ιInf isOpenImmersion_ιFin isOpenImmersion_ιInf mem_range_ιFin_or_mem_range_ιInf chartFinOpen chartInfOpen"
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section ChartIntersection

variable (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem ιFin_apply_eq_ιInf_apply_iff (a : ↥(XFin R F j)) (b : ↥(XInf R F j)) :
    (ιFin R F j).base a = (ιInf R F j).base b ↔ ∃ m : ↥(XMid R F j), (fFin R F j).base m = a ∧ (fInf R F j).base m = b := by
  have h := Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin R F j) (fInf R F j))
    (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := a) (xj := b)
  have h' : (ιFin R F j).base a = (ιInf R F j).base b ↔
      ∃ (k : WalkingSpan) (fi : k ⟶ WalkingSpan.left) (fj : k ⟶ WalkingSpan.right)
        (x : ↥((span (fFin R F j) (fInf R F j)).obj k)),
        ((span (fFin R F j) (fInf R F j)).map fi).base x = a ∧ ((span (fFin R F j) (fInf R F j)).map fj).base x = b := h
  rw [h']
  constructor
  · rintro ⟨k, fi, fj, x, ha, hb⟩
    rcases k with (_ | _ | _)
    · obtain rfl : fi = WidePushoutShape.Hom.init _ := Subsingleton.elim _ _
      obtain rfl : fj = WidePushoutShape.Hom.init _ := Subsingleton.elim _ _
      exact ⟨x, ha, hb⟩
    · change WidePushoutShape.Hom _ _ at fj; cases fj
    · change WidePushoutShape.Hom _ _ at fi; cases fi
  · rintro ⟨m, ha, hb⟩
    exact ⟨WalkingSpan.zero, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, m, ha, hb⟩

theorem ιInf_apply_mem_range_ιFin_iff (b : ↥(XInf R F j)) :
    (ιInf R F j).base b ∈ Set.range (ιFin R F j).base ↔ b ∈ Set.range (fInf R F j).base := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨m, -, hm⟩ := (ιFin_apply_eq_ιInf_apply_iff R F j a b).mp ha
    exact ⟨m, hm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(fFin R F j).base m, (ιFin_apply_eq_ιInf_apply_iff R F j _ _).mpr ⟨m, rfl, rfl⟩⟩

theorem ιFin_apply_mem_range_ιInf_iff (a : ↥(XFin R F j)) :
    (ιFin R F j).base a ∈ Set.range (ιInf R F j).base ↔ a ∈ Set.range (fFin R F j).base := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨m, hm, -⟩ := (ιFin_apply_eq_ιInf_apply_iff R F j a b).mp hb.symm
    exact ⟨m, hm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(fInf R F j).base m, ((ιFin_apply_eq_ιInf_apply_iff R F j _ _).mpr ⟨m, rfl, rfl⟩).symm⟩

set_option synthInstance.maxHeartbeats 1600000 in

theorem range_fInf :
    Set.range (fInf R F j).base = (PrimeSpectrum.basicOpen (jInvChartInf R F j) : Set (PrimeSpectrum ↥(chartAlgInf R F j))) := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jInvChartInf R F j)

set_option synthInstance.maxHeartbeats 1600000 in

theorem range_fFin :
    Set.range (fFin R F j).base = (PrimeSpectrum.basicOpen (jChartFin R F j) : Set (PrimeSpectrum ↥(chartAlgFin R F j))) := by
  letI := (inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jChartFin R F j)

theorem ιInf_preimage_chartFinOpen_and_ιFin_preimage_chartInfOpen :
    ιInf R F j ⁻¹ᵁ chartFinOpen R F j = PrimeSpectrum.basicOpen (jInvChartInf R F j) ∧
    ιFin R F j ⁻¹ᵁ chartInfOpen R F j = PrimeSpectrum.basicOpen (jChartFin R F j) := by
  constructor
  · apply TopologicalSpace.Opens.ext
    ext b
    change (ιInf R F j).base b ∈ Set.range (ιFin R F j).base ↔ b ∈ (PrimeSpectrum.basicOpen (jInvChartInf R F j) : Set (PrimeSpectrum ↥(chartAlgInf R F j)))
    rw [ιInf_apply_mem_range_ιFin_iff, range_fInf]
    exact Iff.rfl
  · apply TopologicalSpace.Opens.ext
    ext a
    change (ιFin R F j).base a ∈ Set.range (ιInf R F j).base ↔ a ∈ (PrimeSpectrum.basicOpen (jChartFin R F j) : Set (PrimeSpectrum ↥(chartAlgFin R F j)))
    rw [ιFin_apply_mem_range_ιInf_iff, range_fFin]
    exact Iff.rfl

noncomputable def ΓChartFinIso (V : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens) (hV : V = chartFinOpen R F j) :
    Γ(AlgebraicCurve.TwoChartIntegralModel R F j, V) ≅ CommRingCat.of ↥(chartAlgFin R F j) :=
  (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.mapIso (eqToIso (congrArg Opposite.op hV)) ≪≫
    (IsOpenImmersion.ΓIsoTop (ιFin R F j)).symm ≪≫ Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))

noncomputable def ΓChartInfIso (V : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens) (hV : V = chartInfOpen R F j) :
    Γ(AlgebraicCurve.TwoChartIntegralModel R F j, V) ≅ CommRingCat.of ↥(chartAlgInf R F j) :=
  (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.mapIso (eqToIso (congrArg Opposite.op hV)) ≪≫
    (IsOpenImmersion.ΓIsoTop (ιInf R F j)).symm ≪≫ Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))

theorem isDomain_sections_of_eq_chartFinOpen (V : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens) (hV : V = chartFinOpen R F j) :
    IsDomain Γ(AlgebraicCurve.TwoChartIntegralModel R F j, V) :=
  (ΓChartFinIso R F j V hV).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _

theorem isDomain_sections_of_eq_chartInfOpen (V : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens) (hV : V = chartInfOpen R F j) :
    IsDomain Γ(AlgebraicCurve.TwoChartIntegralModel R F j, V) :=
  (ΓChartInfIso R F j V hV).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _

end ChartIntersection

end AlgebraicCurve.TwoChartIntegralModel

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP infSubgroup Gamma1_le_GammaH qExpFunctionFieldC jqModC transcendental_jqModC finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "pi_chartInf iota0_spec iotaInf iotaInf_spec π pi_chart iota0 comp"
namespace FinPiH
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi.AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel P2MW.S_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi.AlgebraicCurve.TwoChartIntegralModel ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi.ModularCurve ModularCurve.XHDRLevel"

section Pi

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)

abbrev KΓ (Γ : Subgroup SL(2, ℤ)) : Type := ↥(qExpFunctionFieldC ℚ Γ)

set_option synthInstance.maxHeartbeats 1600000 in
theorem iota0_jChartFin :
    𝔛.iota0 (jChartFin (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) = jChartFin (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) := by
  apply Subtype.ext; apply Subtype.ext
  rw [𝔛.iota0_spec, coe_jChartFin, coe_jChartFin, coe_jAt, coe_jAt]

set_option synthInstance.maxHeartbeats 1600000 in
theorem iotaInf_jInvChartInf :
    𝔛.iotaInf (jInvChartInf (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) = jInvChartInf (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) := by
  apply Subtype.ext; apply Subtype.ext
  rw [𝔛.iotaInf_spec, coe_jInvChartInf, coe_jInvChartInf, IntermediateField.coe_inv, IntermediateField.coe_inv, coe_jAt, coe_jAt]

set_option synthInstance.maxHeartbeats 1600000 in
theorem iota0_injective : Function.Injective 𝔛.iota0 := by
  intro a b h
  apply Subtype.ext; apply Subtype.ext
  rw [← 𝔛.iota0_spec a, ← 𝔛.iota0_spec b, h]

set_option synthInstance.maxHeartbeats 1600000 in
theorem iotaInf_injective : Function.Injective 𝔛.iotaInf := by
  intro a b h
  apply Subtype.ext; apply Subtype.ext
  rw [← 𝔛.iotaInf_spec a, ← 𝔛.iotaInf_spec b, h]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem preimage_range_ιFin :
    𝔛.π.1.base ⁻¹' Set.range (ιFin p (ΓN p M H hpM) hj).base = Set.range (ιFin p (ΓM M H) hj).base := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases mem_range_ιFin_or_mem_range_ιInf (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) x with h | ⟨y, rfl⟩
    · exact h
    · have e : 𝔛.π.1.base ((ιInf p (ΓM M H) hj).base y) =
          (ιInf p (ΓN p M H hpM) hj).base ((Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)).base y) := by
        rw [← Scheme.Hom.comp_apply, 𝔛.pi_chartInf, Scheme.Hom.comp_apply]
      have hx' : (ιInf p (ΓN p M H hpM) hj).base ((Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)).base y) ∈
          Set.range (ιFin p (ΓN p M H hpM) hj).base := by rw [← e]; exact hx
      have h0 : (Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)).base y ∈
          ιInf p (ΓN p M H hpM) hj ⁻¹ᵁ chartFinOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) := hx'
      rw [(ιInf_preimage_chartFinOpen_and_ιFin_preimage_chartInfOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)).1] at h0
      have h0' : jInvChartInf (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) ∉
          ((Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)).base y).asIdeal :=
        (PrimeSpectrum.mem_basicOpen _ _).mp h0
      have h1 : jInvChartInf (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) ∉ y.asIdeal := by
        rw [← iotaInf_jInvChartInf 𝔛]
        intro hmem
        exact h0' (Ideal.mem_comap.mpr hmem)
      have h2 : y ∈ ιInf p (ΓM M H) hj ⁻¹ᵁ chartFinOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) := by
        rw [(ιInf_preimage_chartFinOpen_and_ιFin_preimage_chartInfOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj)).1]
        exact (PrimeSpectrum.mem_basicOpen _ _).mpr h1
      exact h2
  · rintro _ ⟨y, rfl⟩
    show 𝔛.π.1.base ((ιFin p (ΓM M H) hj).base y) ∈ Set.range (ιFin p (ΓN p M H hpM) hj).base
    rw [← Scheme.Hom.comp_apply, 𝔛.pi_chart, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem preimage_range_ιInf :
    𝔛.π.1.base ⁻¹' Set.range (ιInf p (ΓN p M H hpM) hj).base = Set.range (ιInf p (ΓM M H) hj).base := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases mem_range_ιFin_or_mem_range_ιInf (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) x with ⟨y, rfl⟩ | h
    · have e : 𝔛.π.1.base ((ιFin p (ΓM M H) hj).base y) =
          (ιFin p (ΓN p M H hpM) hj).base ((Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom)).base y) := by
        rw [← Scheme.Hom.comp_apply, 𝔛.pi_chart, Scheme.Hom.comp_apply]
      have hx' : (ιFin p (ΓN p M H hpM) hj).base ((Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom)).base y) ∈
          Set.range (ιInf p (ΓN p M H hpM) hj).base := by rw [← e]; exact hx
      have h0 : (Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom)).base y ∈
          ιFin p (ΓN p M H hpM) hj ⁻¹ᵁ chartInfOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) := hx'
      rw [(ιInf_preimage_chartFinOpen_and_ιFin_preimage_chartInfOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)).2] at h0
      have h0' : jChartFin (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) ∉
          ((Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom)).base y).asIdeal :=
        (PrimeSpectrum.mem_basicOpen _ _).mp h0
      have h1 : jChartFin (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) ∉ y.asIdeal := by
        rw [← iota0_jChartFin 𝔛]
        intro hmem
        exact h0' (Ideal.mem_comap.mpr hmem)
      have h2 : y ∈ ιFin p (ΓM M H) hj ⁻¹ᵁ chartInfOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) := by
        rw [(ιInf_preimage_chartFinOpen_and_ιFin_preimage_chartInfOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj)).2]
        exact (PrimeSpectrum.mem_basicOpen _ _).mpr h1
      exact h2
    · exact h
  · rintro _ ⟨y, rfl⟩
    show 𝔛.π.1.base ((ιInf p (ΓM M H) hj).base y) ∈ Set.range (ιInf p (ΓN p M H hpM) hj).base
    rw [← Scheme.Hom.comp_apply, 𝔛.pi_chartInf, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

theorem preimage_chartFinOpen :
    𝔛.π.1 ⁻¹ᵁ chartFinOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) = chartFinOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) :=
  TopologicalSpace.Opens.ext (preimage_range_ιFin 𝔛)

theorem preimage_chartInfOpen :
    𝔛.π.1 ⁻¹ᵁ chartInfOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) = chartInfOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) :=
  TopologicalSpace.Opens.ext (preimage_range_ιInf 𝔛)

end Pi

end ModularCurve.XHDRModelAtP.FinPiH

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP infSubgroup Gamma1_le_GammaH qExpFunctionFieldC jqModC transcendental_jqModC finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "pi_chartInf iota0_spec iotaInf iotaInf_spec π pi_chart iota0 comp"
namespace FinPiH
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

p2m_open "AlgebraicCurve.TwoChartIntegralModel P2MW.S_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi.AlgebraicCurve.TwoChartIntegralModel"

set_option maxHeartbeats 32000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem moduleFinite_adjoin_chartAlg (Γ : Subgroup SL(2, ℤ)) (ℓ : ℕ) [Fact ℓ.Prime]
    (s : (KΓ Γ)) (hs : Transcendental ↥(GaloisRep.ratLocalizedAt ℓ) s)
    (hFD_s : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({s} : Set (KΓ Γ))) (KΓ Γ)) :
    letI := (Subalgebra.inclusion (adjoin_le_chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) ({s} : Set (KΓ Γ)))).toRingHom.toAlgebra
    Module.Finite ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) ({s} : Set (KΓ Γ))) ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s})) := by
  classical
  haveI hZlFR : IsFractionRing ↥(GaloisRep.ratLocalizedAt ℓ) ℚ := GaloisRep.isFractionRing_ratLocalizedAt ℓ
  haveI hZlPID : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt ℓ) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ
  have hZlFinj : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ)) := by
    rw [IsScalarTower.algebraMap_eq ↥(GaloisRep.ratLocalizedAt ℓ) ℚ (KΓ Γ)]
    exact (algebraMap ℚ (KΓ Γ)).injective.comp (IsFractionRing.injective ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)
  set A := Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) ({s} : Set (KΓ Γ)) with hA
  set K' := IntermediateField.adjoin ℚ ({s} : Set (KΓ Γ)) with hK'def
  haveI hFD' : FiniteDimensional ↥K' (KΓ Γ) := hFD_s
  haveI hK'sep : Algebra.IsSeparable ↥K' (KΓ Γ) := inferInstance
  letI algAC : Algebra ↥A ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s})) :=
    (Subalgebra.inclusion (adjoin_le_chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) ({s} : Set (KΓ Γ)))).toRingHom.toAlgebra
  haveI stAC : IsScalarTower ↥(GaloisRep.ratLocalizedAt ℓ) ↥A ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s})) :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext rfl
  haveI stACF : IsScalarTower ↥A ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s})) (KΓ Γ) :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  haveI hIIC : IsIntegralClosure ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s})) ↥A (KΓ Γ) := {
    algebraMap_injective := Subtype.val_injective
    isIntegral_iff := fun {x} => ⟨fun hx => ⟨⟨x, (mem_chartAlg_iff (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (F := KΓ Γ)).mpr hx⟩, rfl⟩,
      fun ⟨y, hy⟩ => hy ▸ (mem_chartAlg_iff (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (F := KΓ Γ)).mp y.2⟩ }
  have haevInj : Function.Injective (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) :=
    transcendental_iff_injective.mp hs
  have hmemA : ∀ p : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ), (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) p ∈ A := fun p => by
    rw [hA, Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ p
  let eA : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ) ≃ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥A :=
    AlgEquiv.ofBijective ((Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s).codRestrict A hmemA)
      ⟨fun p q h => haevInj (Subtype.ext_iff.mp h),
       fun a => by
         have ha : (a : (KΓ Γ)) ∈ (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s).range := by
           rw [← Algebra.adjoin_singleton_eq_range_aeval, ← hA]; exact a.2
         obtain ⟨p, hp⟩ := ha; exact ⟨p, Subtype.ext hp⟩⟩
  haveI hANoeth : IsNoetherianRing ↥A :=
    isNoetherianRing_of_ringEquiv (Polynomial ↥(GaloisRep.ratLocalizedAt ℓ)) eA.toRingEquiv
  haveI hADom : IsDomain ↥A := inferInstance
  haveI hAUfm : UniqueFactorizationMonoid ↥A :=
    MulEquiv.uniqueFactorizationMonoid eA.toRingEquiv.toMulEquiv inferInstance
  haveI hAIIC : IsIntegrallyClosed ↥A := UniqueFactorizationMonoid.instIsIntegrallyClosed
  have hAK' : ∀ a : ↥A, (a : (KΓ Γ)) ∈ K' := fun a =>
    Algebra.adjoin_induction
      (fun y hy => Set.mem_singleton_iff.mp hy ▸ IntermediateField.mem_adjoin_simple_self ℚ s)
      (fun r => K'.algebraMap_mem (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ r))
      (fun _ _ _ _ ha hb => add_mem ha hb)
      (fun _ _ _ _ ha hb => mul_mem ha hb)
      a.2
  let ιAK : ↥A →+* ↥K' := (Subalgebra.val A).toRingHom.codRestrict K'.toSubring (fun a => hAK' a)
  letI algAK : Algebra ↥A ↥K' := ιAK.toAlgebra
  haveI stAKF : IsScalarTower ↥A ↥K' (KΓ Γ) := IsScalarTower.of_algebraMap_eq fun a => rfl
  haveI stZlAK : IsScalarTower ↥(GaloisRep.ratLocalizedAt ℓ) ↥A ↥K' :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (Subtype.ext rfl)
  have hιAKinj : Function.Injective (algebraMap ↥A ↥K') := fun a b h =>
    Subtype.ext (congrArg (Subtype.val : ↥K' → (KΓ Γ)) h)
  have haevNorm : ∀ p : Polynomial ℚ, ∃ b ∈ nonZeroDivisors ↥(GaloisRep.ratLocalizedAt ℓ),
      (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s)
        (IsLocalization.integerNormalization (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt ℓ)) p) =
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) b) * (Polynomial.aeval (R := ℚ) s) p := by
    intro p
    obtain ⟨b, hb, hbp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt ℓ)) p
    refine ⟨b, hb, ?_⟩
    rw [← Polynomial.aeval_map_algebraMap ℚ s
        (IsLocalization.integerNormalization (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt ℓ)) p), hbp,
      Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt ℓ) ℚ (Polynomial ℚ) b,
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt ℓ) ℚ (KΓ Γ)]
  haveI hAFR : IsFractionRing ↥A ↥K' := by
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨a, ha⟩
      exact isUnit_iff_ne_zero.mpr fun h0 => (mem_nonZeroDivisors_iff_ne_zero.mp ha)
        (hιAKinj (h0.trans (map_zero _).symm))
    · intro k
      obtain ⟨r, t, hrt⟩ :=
        (IntermediateField.mem_adjoin_simple_iff ℚ (α := s) (k : (KΓ Γ))).mp (hK'def ▸ k.2)
      obtain ⟨br, hbr, hbrr⟩ := haevNorm r
      obtain ⟨bt, hbt, hbtt⟩ := haevNorm t
      set r' := IsLocalization.integerNormalization (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt ℓ)) r
      set t' := IsLocalization.integerNormalization (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt ℓ)) t
      by_cases ht0 : (Polynomial.aeval (R := ℚ) s) t = 0
      · refine ⟨⟨0, 1⟩, ?_⟩
        have hk0 : k = 0 := Subtype.ext (by
          show (k : (KΓ Γ)) = 0; rw [hrt, ht0, div_zero])
        simp [hk0]
      · set ar : ↥A := ⟨(Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) r', hmemA r'⟩
        set at' : ↥A := ⟨(Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) t', hmemA t'⟩
        set abr : ↥A := algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥A br with habr
        set abt : ↥A := algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥A bt with habt
        have hat'nz : at' ≠ 0 := fun h0 => by
          have h0F : (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) t' = 0 :=
            congrArg (Subtype.val : ↥A → (KΓ Γ)) h0
          rw [hbtt] at h0F
          rcases mul_eq_zero.mp h0F with hc | hc
          · exact (mem_nonZeroDivisors_iff_ne_zero.mp hbt) (hZlFinj (by rw [hc, map_zero]))
          · exact ht0 hc
        have hZlAinj : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥A) := fun a b h =>
          hZlFinj (congrArg (Subtype.val : ↥A → (KΓ Γ)) h)
        have habrnz : abr ≠ 0 := fun h0 =>
          (mem_nonZeroDivisors_iff_ne_zero.mp hbr) (hZlAinj (by rw [← habr, h0, map_zero]))
        refine ⟨⟨abt * ar, ⟨abr * at',
          mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero habrnz hat'nz)⟩⟩, ?_⟩
        apply Subtype.ext
        show (k : (KΓ Γ)) * ((Subtype.val : ↥A → (KΓ Γ)) (abr * at')) =
             (Subtype.val : ↥A → (KΓ Γ)) (abt * ar)
        have hc1 : ((abr : ↥A) : (KΓ Γ)) = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) br :=
          (IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt ℓ) ↥A (KΓ Γ) br).symm
        have hc2 : ((abt : ↥A) : (KΓ Γ)) = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) bt :=
          (IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt ℓ) ↥A (KΓ Γ) bt).symm
        simp only [Subalgebra.coe_mul, hc1, hc2,
          show ((ar : ↥A) : (KΓ Γ)) = (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) r' from rfl,
          show ((at' : ↥A) : (KΓ Γ)) = (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) t' from rfl,
          hbrr, hbtt, hrt]
        rw [div_mul_eq_mul_div, div_eq_iff ht0]
        ring
    · intro a b hab
      exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; exact hιAKinj hab⟩
  exact IsIntegralClosure.finite ↥A ↥K' (KΓ Γ) ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s}))

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem finite_and_finitePresentation_of_apply_eq {Γ Γ' : Subgroup SL(2, ℤ)} (ℓ : ℕ) [Fact ℓ.Prime]
    (s : (KΓ Γ)) (s' : (KΓ Γ'))
    (hs' : Transcendental ↥(GaloisRep.ratLocalizedAt ℓ) s')
    (hFD' : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({s'} : Set (KΓ Γ'))) (KΓ Γ'))
    (hNoeth : IsNoetherianRing ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s})))
    (φ : ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s})) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ') {s'})))
    (hφ : φ ⟨s, subset_chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) _ rfl⟩ = ⟨s', subset_chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ') _ rfl⟩) :
    φ.toRingHom.Finite ∧ φ.toRingHom.FinitePresentation := by
  classical

  let fA : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s})) :=
    Polynomial.aeval (⟨s, subset_chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) _ rfl⟩ : ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s})))
  let fM : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ') {s'})) :=
    Polynomial.aeval (⟨s', subset_chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ') _ rfl⟩ : ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ') {s'})))

  have hcomp : φ.comp fA = fM := by
    apply Polynomial.algHom_ext
    simp only [fA, fM, AlgHom.comp_apply, Polynomial.aeval_X, hφ]

  set A' := Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) ({s'} : Set (KΓ Γ')) with hA'
  have hmemA' : ∀ p : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ),
      (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s') p ∈ A' := fun p => by
    rw [hA', Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ p
  let incl : ↥A' →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥((chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ') {s'})) :=
    Subalgebra.inclusion (adjoin_le_chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ') ({s'} : Set (KΓ Γ')))
  let cr : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥A' :=
    (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s').codRestrict A' hmemA'
  have htow : fM = incl.comp cr := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply]
    apply Subtype.ext
    simp only [fM, incl, cr, Polynomial.aeval_X, Subalgebra.coe_inclusion, AlgHom.coe_codRestrict]
  have hincl : incl.toRingHom.Finite := moduleFinite_adjoin_chartAlg Γ' ℓ s' hs' hFD'
  have hcr : cr.toRingHom.Finite := by
    refine RingHom.Finite.of_surjective _ fun a => ?_
    have ha : (a : (KΓ Γ')) ∈
        (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s').range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ← hA']; exact a.2
    obtain ⟨p, hp⟩ := ha
    exact ⟨p, Subtype.ext hp⟩
  have hfM : fM.toRingHom.Finite := by
    have e : fM.toRingHom = incl.toRingHom.comp cr.toRingHom := by rw [htow]; rfl
    rw [e]
    exact hincl.comp hcr
  have hfin : φ.toRingHom.Finite := by
    refine RingHom.Finite.of_comp_finite (f := fA.toRingHom) ?_
    have e : φ.toRingHom.comp fA.toRingHom = fM.toRingHom := by rw [← hcomp]; rfl
    rw [e]
    exact hfM
  refine ⟨hfin, ?_⟩
  haveI := hNoeth
  exact RingHom.FinitePresentation.of_finiteType.mp hfin.finiteType

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem isNoetherianRing_chartAlg (Γ : Subgroup SL(2, ℤ)) (ℓ : ℕ) [Fact ℓ.Prime]
    (s : KΓ Γ) (hs : Transcendental ↥(GaloisRep.ratLocalizedAt ℓ) s)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({s} : Set (KΓ Γ))) (KΓ Γ)) :
    IsNoetherianRing ↥(chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s}) := by
  classical
  haveI : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt ℓ) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ
  let A := Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) ({s} : Set (KΓ Γ))
  letI : Algebra ↥A ↥(chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s}) :=
    (Subalgebra.inclusion (adjoin_le_chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) ({s} : Set (KΓ Γ)))).toRingHom.toAlgebra
  haveI : IsScalarTower ↥(GaloisRep.ratLocalizedAt ℓ) ↥A ↥(chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s}) :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext rfl
  haveI : Module.Finite ↥A ↥(chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s}) := moduleFinite_adjoin_chartAlg Γ ℓ s hs hFD
  have hA : Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥A := by
    rw [← Subalgebra.fg_iff_finiteType]
    have := Subalgebra.fg_adjoin_finset (R := ↥(GaloisRep.ratLocalizedAt ℓ)) ({s} : Finset (KΓ Γ))
    rwa [Finset.coe_singleton] at this
  haveI : Algebra.FiniteType ↥A ↥(chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s}) := Module.Finite.finiteType _
  have h : Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) (KΓ Γ) {s}) := hA.trans inferInstance
  exact Algebra.FiniteType.isNoetherianRing ↥(GaloisRep.ratLocalizedAt ℓ) _

theorem transcendental_of_ringHom {A B : Type*} [Field A] [Field B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →+* B) {a : A} (h : Transcendental ℚ (f a)) : Transcendental ℚ a := by
  intro halg
  apply h
  obtain ⟨P, hP0, hP⟩ := halg
  refine ⟨P, hP0, ?_⟩
  have := Polynomial.aeval_algHom_apply f.toRatAlgHom a P
  rw [hP, map_zero] at this
  exact this

theorem finiteDimensional_adjoin_congr_inst {F : Type*} [Field F] {i₁ i₂ : Algebra ℚ F} (j : F)
    (h : letI := i₁; FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set F)) F) :
    letI := i₂; FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set F)) F := by
  have : i₁ = i₂ := Subsingleton.elim _ _
  subst this
  exact h

set_option synthInstance.maxHeartbeats 1600000 in
theorem transcendental_jAt (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Transcendental ↥(GaloisRep.ratLocalizedAt ℓ) (jAt Γ hj : KΓ Γ) ∧ Transcendental ↥(GaloisRep.ratLocalizedAt ℓ) ((jAt Γ hj)⁻¹ : KΓ Γ) := by
  haveI : IsFractionRing ↥(GaloisRep.ratLocalizedAt ℓ) ℚ := GaloisRep.isFractionRing_ratLocalizedAt ℓ
  have htjℚ : Transcendental ℚ (jAt Γ hj : KΓ Γ) :=
    transcendental_of_ringHom (SubringClass.subtype (qExpFunctionFieldC ℚ Γ))
      (ModularCurve.transcendental_jqModC ℚ :
        Transcendental ℚ (SubringClass.subtype (qExpFunctionFieldC ℚ Γ) (jAt Γ hj)))
  have htj : Transcendental ↥(GaloisRep.ratLocalizedAt ℓ) (jAt Γ hj : KΓ Γ) :=
    fun h => htjℚ ((IsFractionRing.isAlgebraic_iff ↥(GaloisRep.ratLocalizedAt ℓ) ℚ (KΓ Γ)).mp h)
  refine ⟨htj, fun halg => ?_⟩
  have := halg.inv; rw [inv_inv] at this; exact htj this

set_option synthInstance.maxHeartbeats 1600000 in
theorem finiteDimensional_adjoin_jAt (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    FiniteDimensional ↥(IntermediateField.adjoin ℚ ({(jAt Γ hj : KΓ Γ)} : Set (KΓ Γ))) (KΓ Γ) ∧
    FiniteDimensional ↥(IntermediateField.adjoin ℚ ({((jAt Γ hj)⁻¹ : KΓ Γ)} : Set (KΓ Γ))) (KΓ Γ) := by
  have h0 := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ Γ hT
    Γ le_rfl (fun γ h => Or.inl h) (jAt Γ hj) (coe_jAt _ hj)).1
  have h1 : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({(jAt Γ hj : KΓ Γ)} : Set (KΓ Γ))) (KΓ Γ) :=
    finiteDimensional_adjoin_congr_inst _ h0
  refine ⟨h1, ?_⟩
  have hK : IntermediateField.adjoin ℚ ({((jAt Γ hj)⁻¹ : KΓ Γ)} : Set (KΓ Γ)) =
      IntermediateField.adjoin ℚ ({(jAt Γ hj : KΓ Γ)} : Set (KΓ Γ)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      exact Set.singleton_subset_iff.mpr
        ((IntermediateField.adjoin ℚ ({(jAt Γ hj : KΓ Γ)} : Set (KΓ Γ))).inv_mem
          (IntermediateField.mem_adjoin_simple_self ℚ (jAt Γ hj : KΓ Γ)))
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx; obtain rfl := hx
      have h2 := (IntermediateField.adjoin ℚ {((jAt Γ hj)⁻¹ : KΓ Γ)}).inv_mem
        (IntermediateField.mem_adjoin_simple_self ℚ ((jAt Γ hj)⁻¹ : KΓ Γ))
      rwa [inv_inv] at h2
  rw [hK]
  exact h1

theorem Gamma1_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

theorem finiteIndex_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := inferInstance
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem T_mem_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  apply Gamma1_le_GammaH
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T]

theorem exists_iso_comp_pullback_snd_eq {V X U Y : Scheme.{0}} (f : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g]
    (i : V ⟶ X) [IsOpenImmersion i] (φ : V ⟶ U) (hsq : i ≫ f = φ ≫ g)
    (hrange : f.base ⁻¹' Set.range g.base = Set.range i.base) :
    ∃ e : V ≅ pullback f g, e.hom ≫ pullback.snd f g = φ := by
  have hr : Set.range i.base = Set.range (pullback.fst f g).base := by
    rw [Scheme.Pullback.range_fst, hrange]
  refine ⟨IsOpenImmersion.isoOfRangeEq i (pullback.fst f g) hr, ?_⟩
  rw [← cancel_mono g, Category.assoc, ← pullback.condition, ← Category.assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, hsq]

end ModularCurve.XHDRModelAtP.FinPiH

end

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi.AlgebraicCurve IsLocalRing AlgebraicCurve.TwoChartIntegralModel P2MW.S_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi.AlgebraicCurve.TwoChartIntegralModel ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi.ModularCurve.XHDRModelAtP.FinPiH"

open scoped MatrixGroups

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    IsFinite 𝔛.π.1 ∧ LocallyOfFinitePresentation 𝔛.π.1 := by
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : IsPrincipalIdealRing (R p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI : (ΓM M H).FiniteIndex := finiteIndex_GammaH M H
  haveI : (ΓN p M H hpM).FiniteIndex := finiteIndex_GammaH (M / p) (infSubgroup p M H hpM)
  have hTM : ModularGroup.T ∈ ΓM M H := T_mem_GammaH M H
  have hTN : ModularGroup.T ∈ ΓN p M H hpM := T_mem_GammaH (M / p) (infSubgroup p M H hpM)

  obtain ⟨htjN, htjiN⟩ := transcendental_jAt (ΓN p M H hpM) hj p
  obtain ⟨htjM, htjiM⟩ := transcendental_jAt (ΓM M H) hj p
  obtain ⟨hFDN, hFDNi⟩ := finiteDimensional_adjoin_jAt (ΓN p M H hpM) hTN hj
  obtain ⟨hFDM, hFDMi⟩ := finiteDimensional_adjoin_jAt (ΓM M H) hTM hj

  have hNoeth0 : IsNoetherianRing ↥(chartAlgFin p (ΓN p M H hpM) hj) :=
    isNoetherianRing_chartAlg (ΓN p M H hpM) p (jAt (ΓN p M H hpM) hj) htjN hFDN
  have hNoethInf : IsNoetherianRing ↥(chartAlgInf p (ΓN p M H hpM) hj) :=
    isNoetherianRing_chartAlg (ΓN p M H hpM) p ((jAt (ΓN p M H hpM) hj)⁻¹) htjiN hFDNi

  have hj0 : 𝔛.iota0 ⟨jAt (ΓN p M H hpM) hj, subset_chartAlg (R p) (KΓ (ΓN p M H hpM)) _ rfl⟩ =
      ⟨jAt (ΓM M H) hj, subset_chartAlg (R p) (KΓ (ΓM M H)) _ rfl⟩ := by
    apply Subtype.ext; apply Subtype.ext
    rw [𝔛.iota0_spec]
    show ((jAt (ΓN p M H hpM) hj : KΓ (ΓN p M H hpM)) : LaurentSeries ℚ) = ((jAt (ΓM M H) hj : KΓ (ΓM M H)) : LaurentSeries ℚ)
    rw [coe_jAt, coe_jAt]
  have hjinf : 𝔛.iotaInf ⟨(jAt (ΓN p M H hpM) hj)⁻¹, subset_chartAlg (R p) (KΓ (ΓN p M H hpM)) _ rfl⟩ =
      ⟨(jAt (ΓM M H) hj)⁻¹, subset_chartAlg (R p) (KΓ (ΓM M H)) _ rfl⟩ := by
    apply Subtype.ext; apply Subtype.ext
    rw [𝔛.iotaInf_spec]
    show (((jAt (ΓN p M H hpM) hj)⁻¹ : KΓ (ΓN p M H hpM)) : LaurentSeries ℚ) = (((jAt (ΓM M H) hj)⁻¹ : KΓ (ΓM M H)) : LaurentSeries ℚ)
    rw [IntermediateField.coe_inv, IntermediateField.coe_inv, coe_jAt, coe_jAt]

  obtain ⟨hf0, hfp0⟩ := finite_and_finitePresentation_of_apply_eq p (jAt (ΓN p M H hpM) hj) (jAt (ΓM M H) hj) htjM
    hFDM hNoeth0 𝔛.iota0 hj0
  obtain ⟨hfi, hfpi⟩ := finite_and_finitePresentation_of_apply_eq p ((jAt (ΓN p M H hpM) hj)⁻¹) ((jAt (ΓM M H) hj)⁻¹) htjiM
    hFDMi hNoethInf 𝔛.iotaInf hjinf
  have SF0 : IsFinite (Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom)) := (IsFinite.SpecMap_iff _).mpr hf0
  have SP0 : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom)) := HasRingHomProperty.Spec_iff.mpr hfp0
  have SFi : IsFinite (Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)) := (IsFinite.SpecMap_iff _).mpr hfi
  have SPi : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)) := HasRingHomProperty.Spec_iff.mpr hfpi

  let 𝒰 : (X p (ΓN p M H hpM) hj).OpenCover :=
    Scheme.Cover.mkOfCovers Bool (fun b => cond b (XFin (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) (XInf (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)))
      (fun b => match b with | true => ιFin p (ΓN p M H hpM) hj | false => ιInf p (ΓN p M H hpM) hj)
      (fun x => by
        rcases mem_range_ιFin_or_mem_range_ιInf (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact ⟨true, y, hy⟩
        · exact ⟨false, y, hy⟩)
      (fun b => by
        cases b
        · exact AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)
        · exact AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj))

  obtain ⟨eF, heF⟩ := exists_iso_comp_pullback_snd_eq 𝔛.π.1 (ιFin p (ΓN p M H hpM) hj) (ιFin p (ΓM M H) hj)
    (Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom)) 𝔛.pi_chart (preimage_range_ιFin 𝔛)
  obtain ⟨eI, heI⟩ := exists_iso_comp_pullback_snd_eq 𝔛.π.1 (ιInf p (ΓN p M H hpM) hj) (ιInf p (ΓM M H) hj)
    (Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)) 𝔛.pi_chartInf (preimage_range_ιInf 𝔛)
  have hF : pullback.snd 𝔛.π.1 (ιFin p (ΓN p M H hpM) hj) = eF.inv ≫ Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom) := by
    rw [← heF, eF.inv_hom_id_assoc]
  have hI : pullback.snd 𝔛.π.1 (ιInf p (ΓN p M H hpM) hj) = eI.inv ≫ Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom) := by
    rw [← heI, eI.inv_hom_id_assoc]
  constructor
  · refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun b => ?_
    cases b
    · show IsFinite (pullback.snd 𝔛.π.1 (ιInf p (ΓN p M H hpM) hj)); rw [hI]; infer_instance
    · show IsFinite (pullback.snd 𝔛.π.1 (ιFin p (ΓN p M H hpM) hj)); rw [hF]; infer_instance
  · refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun b => ?_
    cases b
    · show LocallyOfFinitePresentation (pullback.snd 𝔛.π.1 (ιInf p (ΓN p M H hpM) hj)); rw [hI]; infer_instance
    · show LocallyOfFinitePresentation (pullback.snd 𝔛.π.1 (ιFin p (ΓN p M H hpM) hj)); rw [hF]; infer_instance

#print axioms solution

end S_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi (solution)

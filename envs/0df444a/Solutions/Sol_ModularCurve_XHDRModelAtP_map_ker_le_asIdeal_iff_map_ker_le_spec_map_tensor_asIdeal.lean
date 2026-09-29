-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.map_ker_le_asIdeal_iff_map_ker_le_spec_map_tensor_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f40fd11b-37ba-56d0-9422-0d0040020a5c

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_range_comp_zero_iff_map_ker_le
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia
import Theorems.Thm_ModularCurve_XHDRModelAtP_range_comp_zero_fibreMap_dia
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_map_ker_le_asIdeal_iff_map_ker_le_spec_map_tensor_asIdeal
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_map_ker_le_asIdeal_iff_map_ker_le_spec_map_tensor_asIdeal.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_map_ker_le_asIdeal_iff_map_ker_le_spec_map_tensor_asIdeal.ModularCurve.XHDRLevel"
open scoped MatrixGroups TensorProduct

namespace ModularCurve p2m_export "ModularCurve" "XHDRModelAtP qExpFunctionFieldC coeffMap jqModC XHDRModelAtP.mem_range_comp_zero_iff_map_ker_le XHDRModelAtP.exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia XHDRModelAtP.range_comp_zero_fibreMap_dia" namespace XHDRLevel p2m_export "ModularCurve.XHDRLevel" "R X toBase chartAlgInf ιInf fibre fibreMap overOfIso ΓM" end ModularCurve.XHDRLevel
p2m_open_scoped "ModularCurve ModularCurve.XHDRLevel" in

theorem ModularCurve.XHDRLevel.isIso_fibreMap_overOfIso {p : ℕ} {Γ : Subgroup SL(2, ℤ)}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (w : X p Γ hj ≅ X p Γ hj) (hw : w.hom ≫ toBase p Γ hj = toBase p Γ hj) {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    IsIso (fibreMap (overOfIso w hw) toκ) := by
  dsimp only [fibreMap, overOfIso]
  infer_instance

theorem mem_iff_apply_mem_of_image_eq {α : Type*} {F : α → α} (hF : Function.Injective F) {S : Set α}
    (hS : F '' S = S) (x : α) : x ∈ S ↔ F x ∈ S := by
  constructor
  · intro hx; rw [← hS]; exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hS] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← hF hyx]

theorem solution
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) (IsLocalRing.ResidueField ↥A)]
    (halg : algebraMap (R p) (IsLocalRing.ResidueField ↥A) = (IsLocalRing.residue ↥A).comp ρ)
    (red : ↥(chartAlgInf p (ΓM M H) hj) →+* LaurentSeries (IsLocalRing.ResidueField ↥A))
    (hred : ∀ (b : ↥(chartAlgInf p (ΓM M H) hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        red b = coeffMap ((IsLocalRing.residue ↥A).comp ρ) y)
    (d : (ZMod M)ˣ)
    (σ : ↥(chartAlgInf p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj))
    (hdia : ιInf p (ΓM M H) hj ≫ (𝔓.dia d).hom =
      Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ ιInf p (ΓM M H) hj)
    (z : ↥(Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))))) :
    Ideal.map (Algebra.TensorProduct.includeRight :
          ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))
        (RingHom.ker red) ≤ z.asIdeal ↔
      Ideal.map (Algebra.TensorProduct.includeRight :
          ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))
        (RingHom.ker red) ≤
        ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id (R p) (IsLocalRing.ResidueField ↥A)) (σ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] _)).toRingHom)).base z).asIdeal := by
  obtain ⟨c', hc'fst, hc'snd, hint⟩ :=
    ModularCurve.XHDRModelAtP.exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia 𝔓 A hA ρ hρ halg d σ hdia
  have hz := ModularCurve.XHDRModelAtP.mem_range_comp_zero_iff_map_ker_le 𝔓 A hA ρ hρ halg red hred c' hc'fst hc'snd z
  have hz' := ModularCurve.XHDRModelAtP.mem_range_comp_zero_iff_map_ker_le 𝔓 A hA ρ hρ halg red hred c' hc'fst hc'snd
    ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
      (AlgHom.id (R p) (IsLocalRing.ResidueField ↥A))
      (σ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj))).toRingHom)).base z)
  obtain ⟨Fm, hFm⟩ : ∃ Fm, Fm = fibreMap (overOfIso (𝔓.dia d) (𝔓.dia_over d)) ((IsLocalRing.residue ↥A).comp ρ) := ⟨_, rfl⟩
  rw [← hFm] at hint
  have himg := congrArg (fun f => f.base z) hint
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at himg

  haveI : IsIso Fm := by
    rw [hFm]
    exact ModularCurve.XHDRLevel.isIso_fibreMap_overOfIso _ _ _
  have e : ∀ x, (inv Fm).base (Fm.base x) = x := by
    intro x
    rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, IsIso.hom_inv_id]
    simp
  have hinj : Function.Injective Fm.base := by
    intro a b h
    calc a = (inv Fm).base (Fm.base a) := (e a).symm
      _ = (inv Fm).base (Fm.base b) := by rw [h]
      _ = b := e b
  have hS : Fm.base '' Set.range (𝔓.comp A hA ρ hρ 0).base = Set.range (𝔓.comp A hA ρ hρ 0).base := by
    have := ModularCurve.XHDRModelAtP.range_comp_zero_fibreMap_dia 𝔓 A hA ρ hρ d
    rw [← hFm] at this
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp] at this
    exact this
  have key : c'.base z ∈ Set.range (𝔓.comp A hA ρ hρ 0).base ↔
      Fm.base (c'.base z) ∈ Set.range (𝔓.comp A hA ρ hρ 0).base :=
    mem_iff_apply_mem_of_image_eq hinj hS _
  rw [← himg] at key
  exact hz.symm.trans (key.trans hz')

end S_ModularCurve_XHDRModelAtP_map_ker_le_asIdeal_iff_map_ker_le_spec_map_tensor_asIdeal
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_map_ker_le_asIdeal_iff_map_ker_le_spec_map_tensor_asIdeal (solution)

-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.isFinite_and_locallyOfFinitePresentation_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/05f72605-4276-5ac9-8db2-40094a2398b2

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_IgusaScheme_iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen
import Theorems.Thm_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_specMap_iota
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_pi
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_pi.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel.neZero_mul DRModelPackageLevel IgusaScheme IgusaScheme.isOpenImmersion_ιFin IgusaScheme.isOpenImmersion_ιInf IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen DRModelPackageLevel.isFinite_and_locallyOfFinitePresentation_specMap_iota"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "neZero_mul pi_chart pi_chartInf iota0 iota0_spec iotaInf_spec π iotaInf isFinite_and_locallyOfFinitePresentation_specMap_iota"
namespace F1Assembly
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

attribute [local instance] DRModelPackageLevel.neZero_mul

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔓 : DRModelPackageLevel N₀ q hqN)

set_option synthInstance.maxHeartbeats 1600000 in
theorem iota0_jChartFin : 𝔓.iota0 (jChartFin N₀ q) = jChartFin (N₀ * q) q := by
  apply Subtype.ext; apply Subtype.ext
  rw [𝔓.iota0_spec (jChartFin N₀ q), coe_jChartFin, coe_jChartFin, coe_jFull, coe_jFull]

set_option synthInstance.maxHeartbeats 1600000 in
theorem iotaInf_jInvChartInf : 𝔓.iotaInf (jInvChartInf N₀ q) = jInvChartInf (N₀ * q) q := by
  apply Subtype.ext; apply Subtype.ext
  rw [𝔓.iotaInf_spec (jInvChartInf N₀ q), coe_jInvChartInf, coe_jInvChartInf, IntermediateField.coe_inv,
    IntermediateField.coe_inv, coe_jFull, coe_jFull]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem preimage_range_ιFin :
    𝔓.π.1.base ⁻¹' Set.range (ιFin N₀ q).base = Set.range (ιFin (N₀ * q) q).base := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases mem_range_ιFin_or_mem_range_ιInf (N₀ * q) q x with h | ⟨y, rfl⟩
    · exact h
    ·
      have e : 𝔓.π.1.base ((ιInf (N₀ * q) q).base y) =
          (ιInf N₀ q).base ((Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom)).base y) := by
        rw [← Scheme.Hom.comp_apply, 𝔓.pi_chartInf, Scheme.Hom.comp_apply]
      have hx' : (ιInf N₀ q).base ((Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom)).base y) ∈
          Set.range (ιFin N₀ q).base := by rw [← e]; exact hx
      have h0 : (Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom)).base y ∈ ιInf N₀ q ⁻¹ᵁ chartFinOpen N₀ q := hx'
      rw [(ModularCurve.IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen N₀ q).1] at h0
      have h0' : jInvChartInf N₀ q ∉ ((Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom)).base y).asIdeal :=
        (PrimeSpectrum.mem_basicOpen _ _).mp h0
      have h1 : jInvChartInf (N₀ * q) q ∉ y.asIdeal := by
        rw [← iotaInf_jInvChartInf 𝔓]
        intro hmem
        exact h0' (Ideal.mem_comap.mpr hmem)
      have h2 : y ∈ ιInf (N₀ * q) q ⁻¹ᵁ chartFinOpen (N₀ * q) q := by
        rw [(ModularCurve.IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen (N₀ * q) q).1]
        exact (PrimeSpectrum.mem_basicOpen _ _).mpr h1
      exact h2
  · rintro _ ⟨y, rfl⟩
    show 𝔓.π.1.base ((ιFin (N₀ * q) q).base y) ∈ Set.range (ιFin N₀ q).base
    rw [← Scheme.Hom.comp_apply, 𝔓.pi_chart, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem preimage_range_ιInf :
    𝔓.π.1.base ⁻¹' Set.range (ιInf N₀ q).base = Set.range (ιInf (N₀ * q) q).base := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases mem_range_ιFin_or_mem_range_ιInf (N₀ * q) q x with ⟨y, rfl⟩ | h
    · have e : 𝔓.π.1.base ((ιFin (N₀ * q) q).base y) =
          (ιFin N₀ q).base ((Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom)).base y) := by
        rw [← Scheme.Hom.comp_apply, 𝔓.pi_chart, Scheme.Hom.comp_apply]
      have hx' : (ιFin N₀ q).base ((Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom)).base y) ∈
          Set.range (ιInf N₀ q).base := by rw [← e]; exact hx
      have h0 : (Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom)).base y ∈ ιFin N₀ q ⁻¹ᵁ chartInfOpen N₀ q := hx'
      rw [(ModularCurve.IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen N₀ q).2] at h0
      have h0' : jChartFin N₀ q ∉ ((Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom)).base y).asIdeal :=
        (PrimeSpectrum.mem_basicOpen _ _).mp h0
      have h1 : jChartFin (N₀ * q) q ∉ y.asIdeal := by
        rw [← iota0_jChartFin 𝔓]
        intro hmem
        exact h0' (Ideal.mem_comap.mpr hmem)
      have h2 : y ∈ ιFin (N₀ * q) q ⁻¹ᵁ chartInfOpen (N₀ * q) q := by
        rw [(ModularCurve.IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen (N₀ * q) q).2]
        exact (PrimeSpectrum.mem_basicOpen _ _).mpr h1
      exact h2
    · exact h
  · rintro _ ⟨y, rfl⟩
    show 𝔓.π.1.base ((ιInf (N₀ * q) q).base y) ∈ Set.range (ιInf N₀ q).base
    rw [← Scheme.Hom.comp_apply, 𝔓.pi_chartInf, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

theorem exists_iso_comp_pullback_snd_eq {V X U Y : Scheme.{0}} (f : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g]
    (i : V ⟶ X) [IsOpenImmersion i] (φ : V ⟶ U) (hsq : i ≫ f = φ ≫ g)
    (hrange : f.base ⁻¹' Set.range g.base = Set.range i.base) :
    ∃ e : V ≅ pullback f g, e.hom ≫ pullback.snd f g = φ := by
  have hr : Set.range i.base = Set.range (pullback.fst f g).base := by
    rw [Scheme.Pullback.range_fst, hrange]
  refine ⟨IsOpenImmersion.isoOfRangeEq i (pullback.fst f g) hr, ?_⟩
  rw [← cancel_mono g, Category.assoc, ← pullback.condition, ← Category.assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, hsq]

end ModularCurve.DRModelPackageLevel.F1Assembly

open _root_.ModularCurve.DRModelPackageLevel _root_.P2MW.S_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_pi.ModularCurve.DRModelPackageLevel ModularCurve.DRModelPackageLevel.F1Assembly in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) :
    IsFinite 𝔓.π.1 ∧ LocallyOfFinitePresentation 𝔓.π.1 := by
  haveI : NeZero (N₀ * q) := DRModelPackageLevel.neZero_mul N₀ q
  obtain ⟨⟨hf0, hp0⟩, ⟨hfi, hpi⟩⟩ :=
    ModularCurve.DRModelPackageLevel.isFinite_and_locallyOfFinitePresentation_specMap_iota N₀ q hqN 𝔓

  let 𝒰 : (X0 N₀ q).OpenCover :=
    Scheme.Cover.mkOfCovers Bool (fun b => cond b (XFin N₀ q) (XInf N₀ q))
      (fun b => match b with | true => ιFin N₀ q | false => ιInf N₀ q)
      (fun x => by
        rcases mem_range_ιFin_or_mem_range_ιInf N₀ q x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact ⟨true, y, hy⟩
        · exact ⟨false, y, hy⟩)
      (fun b => by
        cases b
        · exact ModularCurve.IgusaScheme.isOpenImmersion_ιInf N₀ q
        · exact ModularCurve.IgusaScheme.isOpenImmersion_ιFin N₀ q)

  obtain ⟨eF, heF⟩ := exists_iso_comp_pullback_snd_eq 𝔓.π.1 (ιFin N₀ q) (ιFin (N₀ * q) q)
    (Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom)) 𝔓.pi_chart (preimage_range_ιFin 𝔓)
  obtain ⟨eI, heI⟩ := exists_iso_comp_pullback_snd_eq 𝔓.π.1 (ιInf N₀ q) (ιInf (N₀ * q) q)
    (Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom)) 𝔓.pi_chartInf (preimage_range_ιInf 𝔓)
  have hF : pullback.snd 𝔓.π.1 (ιFin N₀ q) = eF.inv ≫ Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom) := by
    rw [← heF, eF.inv_hom_id_assoc]
  have hI : pullback.snd 𝔓.π.1 (ιInf N₀ q) = eI.inv ≫ Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom) := by
    rw [← heI, eI.inv_hom_id_assoc]
  constructor
  · refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun b => ?_
    cases b
    · show IsFinite (pullback.snd 𝔓.π.1 (ιInf N₀ q)); rw [hI]; infer_instance
    · show IsFinite (pullback.snd 𝔓.π.1 (ιFin N₀ q)); rw [hF]; infer_instance
  · refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun b => ?_
    cases b
    · show LocallyOfFinitePresentation (pullback.snd 𝔓.π.1 (ιInf N₀ q)); rw [hI]; infer_instance
    · show LocallyOfFinitePresentation (pullback.snd 𝔓.π.1 (ιFin N₀ q)); rw [hF]; infer_instance

end

end S_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_pi
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_pi (solution)

-- Prove2me | solution 1 for ModularCurve.DRLevel.not_isOpen_singleton_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c9c69734-7f83-5c83-8f49-3ff1a1b0482c

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_IgusaScheme_ringKrullDim_localization_chartAlgFin_tensor
import Theorems.Thm_ModularCurve_IgusaScheme_ringKrullDim_localization_chartAlgInf_tensor
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_not_isOpen_singleton_fibre
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open "ModularCurve P2MW.S_ModularCurve_DRLevel_not_isOpen_singleton_fibre.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_not_isOpen_singleton_fibre.ModularCurve.DRLevel"
open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.toBase DRLevel.fibre DRModelPackageLevel IgusaScheme.chartAlgFin IgusaScheme.chartAlgInf IgusaScheme IgusaScheme.ιFin IgusaScheme.ιInf IgusaScheme.ιFin_igusaTo IgusaScheme.ιInf_igusaTo IgusaScheme.mem_range_ιFin_or_mem_range_ιInf IgusaScheme.ringKrullDim_localization_chartAlgFin_tensor IgusaScheme.ringKrullDim_localization_chartAlgInf_tensor IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf"
namespace DRLevel
p2m_export "ModularCurve.DRLevel" "R X toBase fibre"
namespace E3_4383a3d4
p2m_open "ModularCurve.DRLevel ModularCurve"

private theorem exists_isOpen_singleton_spec_tensor
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (A : Type) [CommRing A] [Algebra R A] (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (κ : Type) [CommRing κ] [Algebra R κ]
    (w : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))))
    (hw : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).base w ∈ Set.range ι.base)
    (hopen : IsOpen ({w} : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))))) :
    ∃ x : ↥(Spec (CommRingCat.of (κ ⊗[R] A))), IsOpen ({x} : Set ↥(Spec (CommRingCat.of (κ ⊗[R] A)))) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ A)

  have hcompat : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := A)).toRingHom) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R κ)) := by
    rw [Category.assoc, hι]
    exact sq.w.symm
  let c : Spec (CommRingCat.of (κ ⊗[R] A)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ))) :=
    pullback.lift _ _ hcompat
  have hcfst : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := A)).toRingHom) ≫ ι := pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) :=
    pullback.lift_snd _ _ _
  have s : IsPullback (c ≫ pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ι ≫ f) := by
    rw [hcsnd, hι]
    exact sq
  have H : IsPullback c
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (pullback.fst _ _) ι :=
    IsPullback.of_right s hcfst (IsPullback.of_hasPullback _ _).flip
  have hc : c = H.isoPullback.hom ≫ pullback.fst _ _ := (H.isoPullback_hom_fst).symm
  haveI : IsOpenImmersion c := by rw [hc]; infer_instance
  have hrange : Set.range c.base =
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).base ⁻¹' Set.range ι.base := by
    rw [← Scheme.Pullback.range_fst, hc]
    ext x; constructor
    · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.hom.base y, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.inv.base y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]⟩

  have hw' : w ∈ Set.range c.base := by rw [hrange]; exact hw
  obtain ⟨x, rfl⟩ := hw'
  refine ⟨x, ?_⟩
  have hpre : c.base ⁻¹' {c.base x} = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact c.isOpenEmbedding.injective.eq_iff
  rw [← hpre]
  exact hopen.preimage c.base.hom.continuous

private theorem isMaximal_and_ringKrullDim_eq_zero_of_isOpen_singleton {B : Type} [CommRing B] [IsJacobsonRing B]
    (x : ↥(Spec (CommRingCat.of B))) (hx : IsOpen ({x} : Set ↥(Spec (CommRingCat.of B)))) :
    x.asIdeal.IsMaximal ∧ ringKrullDim (Localization.AtPrime x.asIdeal) = 0 := by
  have hmin : x.asIdeal ∈ minimalPrimes B :=
    PrimeSpectrum.stableUnderGeneralization_singleton.1 hx.stableUnderGeneralization
  have hcl : IsClosed ({x} : Set ↥(Spec (CommRingCat.of B))) := by
    obtain ⟨z, hz, hzcl⟩ := nonempty_inter_closedPoints (Z := ({x} : Set ↥(Spec (CommRingCat.of B)))) ⟨x, rfl⟩
      hx.isLocallyClosed
    obtain rfl : z = x := hz
    exact mem_closedPoints_iff.mp hzcl
  have hmax : x.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).1 hcl
  refine ⟨hmax, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal (Localization.AtPrime x.asIdeal),
    Ideal.height_eq_zero_iff.2 hmin]
  rfl

end ModularCurve.DRLevel.E3_4383a3d4

open ModularCurve.DRLevel.E3_4383a3d4 in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (κ : Type) [Field κ] [CharP κ q] (toκ : DRLevel.R q →+* κ)
    (w : DRLevel.fibre (N₀ := N₀) toκ) : ¬ IsOpen ({w} : Set (DRLevel.fibre (N₀ := N₀) toκ)) := by
  classical
  intro hopen
  letI : Algebra (DRLevel.R q) κ := toκ.toAlgebra
  haveI : Algebra.FiniteType (DRLevel.R q) ↥(IgusaScheme.chartAlgFin (N₀ * q) q) :=
    (ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf (N₀ * q) q).1
  haveI : Algebra.FiniteType (DRLevel.R q) ↥(IgusaScheme.chartAlgInf (N₀ * q) q) :=
    (ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf (N₀ * q) q).2
  haveI : Algebra.FiniteType κ (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) := inferInstance
  haveI : Algebra.FiniteType κ (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q)) := inferInstance
  haveI : IsJacobsonRing (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) :=
    isJacobsonRing_of_finiteType (A := κ)
  haveI : IsJacobsonRing (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q)) :=
    isJacobsonRing_of_finiteType (A := κ)
  have halg : algebraMap (DRLevel.R q) κ = toκ := rfl

  rcases IgusaScheme.mem_range_ιFin_or_mem_range_ιInf (N₀ * q) q
      ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base w) with hfin | hinf
  · obtain ⟨x, hx⟩ := exists_isOpen_singleton_spec_tensor (DRLevel.toBase N₀ q) ↥(IgusaScheme.chartAlgFin (N₀ * q) q)
      (IgusaScheme.ιFin (N₀ * q) q) (IgusaScheme.ιFin_igusaTo (N₀ * q) q) κ w hfin hopen
    obtain ⟨hmax, h0⟩ := isMaximal_and_ringKrullDim_eq_zero_of_isOpen_singleton x hx
    haveI := hmax
    have h1 := ModularCurve.IgusaScheme.ringKrullDim_localization_chartAlgFin_tensor (N₀ * q) q κ x.asIdeal
    rw [h0] at h1
    exact absurd h1 (by decide)
  · obtain ⟨x, hx⟩ := exists_isOpen_singleton_spec_tensor (DRLevel.toBase N₀ q) ↥(IgusaScheme.chartAlgInf (N₀ * q) q)
      (IgusaScheme.ιInf (N₀ * q) q) (IgusaScheme.ιInf_igusaTo (N₀ * q) q) κ w hinf hopen
    obtain ⟨hmax, h0⟩ := isMaximal_and_ringKrullDim_eq_zero_of_isOpen_singleton x hx
    haveI := hmax
    have h1 := ModularCurve.IgusaScheme.ringKrullDim_localization_chartAlgInf_tensor (N₀ * q) q κ x.asIdeal
    rw [h0] at h1
    exact absurd h1 (by decide)

#print axioms solution

end S_ModularCurve_DRLevel_not_isOpen_singleton_fibre
end P2MW
export P2MW.S_ModularCurve_DRLevel_not_isOpen_singleton_fibre (solution)

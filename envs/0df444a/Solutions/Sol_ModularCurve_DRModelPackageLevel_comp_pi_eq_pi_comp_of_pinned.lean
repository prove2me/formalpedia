-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.comp_pi_eq_pi_comp_of_pinned
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/03138b63-9485-5bc5-bf68-117e7f3ac590

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_IgusaScheme_isProper_igusaTo
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_comp_pi_eq_pi_comp_of_pinned
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_comp_pi_eq_pi_comp_of_pinned.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel"

namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.X DRLevel.toBase DRLevel.toBase0 DRModelPackageLevel IgusaScheme.chartAlgFin IgusaScheme IgusaScheme.ιFin qExpand modularFunctionFieldFull IgusaScheme.isProper_igusaTo IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "pi_chart comp isIntegral iota0 iota0_spec π"
namespace PiCompat
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

private theorem isDominant_ιFin (M q : ℕ) [NeZero M] [Fact q.Prime] [IsIntegral (IgusaScheme M q)] :
    IsDominant (IgusaScheme.ιFin M q) :=
  ⟨(IgusaScheme.ιFin M q).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

private theorem comm_of_chart (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) (ℓ : ℕ) [Fact ℓ.Prime] (hqNℓ : ¬ q ∣ N₀ * ℓ)
    (𝔓' : DRModelPackageLevel (N₀ * ℓ) q hqNℓ)
    (π : SchemeHomOver (DRLevel.toBase (N₀ * ℓ) q) (DRLevel.toBase N₀ q))
    (ι : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q))
    (hπ : IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (ρ : SchemeHomOver (DRLevel.toBase0 (N₀ * ℓ) q) (DRLevel.toBase0 N₀ q))
    (κ : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * ℓ) q))
    (hρ : IgusaScheme.ιFin (N₀ * ℓ) q ≫ ρ.1 = Spec.map (CommRingCat.ofHom κ.toRingHom) ≫ IgusaScheme.ιFin N₀ q)
    (hring : ∀ b, ι (𝔓.iota0 b) = 𝔓'.iota0 (κ b)) :
    π.1 ≫ 𝔓.π.1 = 𝔓'.π.1 ≫ ρ.1 := by
  haveI : IsIntegral (DRLevel.X (N₀ * ℓ) q) := 𝔓'.isIntegral
  haveI := (ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf N₀ q).1
  haveI := (ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf N₀ q).2
  haveI : IsProper (DRLevel.toBase0 N₀ q) := ModularCurve.IgusaScheme.isProper_igusaTo N₀ q
  haveI := isDominant_ιFin (N₀ * ℓ * q) q
  have hring' : ι.toRingHom.comp 𝔓.iota0.toRingHom = 𝔓'.iota0.toRingHom.comp κ.toRingHom :=
    RingHom.ext fun b => by simpa using hring b
  refine ext_of_isDominant_of_isSeparated (DRLevel.toBase0 N₀ q) ?_ (IgusaScheme.ιFin (N₀ * ℓ * q) q) ?_
  · rw [Category.assoc, Category.assoc, 𝔓.π.2, π.2, ρ.2, 𝔓'.π.2]
  · calc IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π.1 ≫ 𝔓.π.1
          = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom) ≫
              IgusaScheme.ιFin N₀ q := by
            rw [← Category.assoc, hπ, Category.assoc, 𝔓.pi_chart]
      _ = Spec.map (CommRingCat.ofHom 𝔓'.iota0.toRingHom) ≫ Spec.map (CommRingCat.ofHom κ.toRingHom) ≫
              IgusaScheme.ιFin N₀ q := by
            rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring']
      _ = IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ 𝔓'.π.1 ≫ ρ.1 := by
            rw [← Category.assoc (IgusaScheme.ιFin (N₀ * ℓ * q) q), 𝔓'.pi_chart, Category.assoc, hρ]

end ModularCurve.DRModelPackageLevel.PiCompat

open ModularCurve.DRModelPackageLevel.PiCompat in

theorem solution (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) (ℓ : ℕ) [Fact ℓ.Prime] (hqNℓ : ¬ q ∣ N₀ * ℓ)
    (𝔓' : DRModelPackageLevel (N₀ * ℓ) q hqNℓ)
    (π₁ π₂ : SchemeHomOver (DRLevel.toBase (N₀ * ℓ) q) (DRLevel.toBase N₀ q))
    (ι₁ ι₂ : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q))
    (hι₁ : ∀ b, (((ι₁ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    (hι₂ : ∀ b, (((ι₂ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
        qExpand ℚ ℓ ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    (hπ₁ : IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π₁.1 = Spec.map (CommRingCat.ofHom ι₁.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hπ₂ : IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π₂.1 = Spec.map (CommRingCat.ofHom ι₂.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (ρ₁ ρ₂ : SchemeHomOver (DRLevel.toBase0 (N₀ * ℓ) q) (DRLevel.toBase0 N₀ q))
    (κ₁ κ₂ : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * ℓ) q))
    (hκ₁ : ∀ b, (((κ₁ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hκ₂ : ∀ b, (((κ₂ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ))) : LaurentSeries ℚ) =
        qExpand ℚ ℓ ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hρ₁ : IgusaScheme.ιFin (N₀ * ℓ) q ≫ ρ₁.1 = Spec.map (CommRingCat.ofHom κ₁.toRingHom) ≫ IgusaScheme.ιFin N₀ q)
    (hρ₂ : IgusaScheme.ιFin (N₀ * ℓ) q ≫ ρ₂.1 = Spec.map (CommRingCat.ofHom κ₂.toRingHom) ≫ IgusaScheme.ιFin N₀ q) :
    π₁.1 ≫ 𝔓.π.1 = 𝔓'.π.1 ≫ ρ₁.1 ∧ π₂.1 ≫ 𝔓.π.1 = 𝔓'.π.1 ≫ ρ₂.1 := by
  have coeInj : ∀ {x y : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)},
      (((x : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
      (((y : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) → x = y :=
    fun h => Subtype.ext (Subtype.ext h)
  refine ⟨comm_of_chart N₀ q hqN 𝔓 ℓ hqNℓ 𝔓' π₁ ι₁ hπ₁ ρ₁ κ₁ hρ₁ fun b => coeInj ?_,
    comm_of_chart N₀ q hqN 𝔓 ℓ hqNℓ 𝔓' π₂ ι₂ hπ₂ ρ₂ κ₂ hρ₂ fun b => coeInj ?_⟩
  · rw [hι₁, 𝔓.iota0_spec, 𝔓'.iota0_spec, hκ₁]
  · rw [hι₂, 𝔓.iota0_spec, 𝔓'.iota0_spec, hκ₂]

end S_ModularCurve_DRModelPackageLevel_comp_pi_eq_pi_comp_of_pinned
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_comp_pi_eq_pi_comp_of_pinned (solution)

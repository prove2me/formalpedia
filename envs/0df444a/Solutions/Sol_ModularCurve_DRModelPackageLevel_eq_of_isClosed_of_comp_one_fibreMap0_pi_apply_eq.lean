-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.eq_of_isClosed_of_comp_one_fibreMap0_pi_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/73d89893-a74c-59e7-b5c8-0e55d48f85ec

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_eq_of_isClosed_of_comp_one_fibreMap0_pi_apply_eq
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_eq_of_isClosed_of_comp_one_fibreMap0_pi_apply_eq.ModularCurve ModularCurve.DRLevel"

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel arithFrobC"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "efib Mfib comp efib_iso π comp1_pi_place"
namespace Radicial
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

universe u

theorem mem_closedPoints_inv_apply {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (y : Y)
    (hy : IsClosed ({y} : Set Y)) : (inv e).base y ∈ closedPoints X := by
  rw [mem_closedPoints_iff]
  have : (inv e).base y = (Scheme.homeoOfIso (asIso e)).symm y := rfl
  rw [this, ← Set.image_singleton]
  exact (Scheme.homeoOfIso (asIso e)).symm.isClosed_image.2 hy

theorem apply_inv_apply {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (y : Y) : e.base ((inv e).base y) = y := by
  change (inv e ≫ e).base y = y
  rw [IsIso.inv_hom_id]
  rfl

end ModularCurve.DRModelPackageLevel.Radicial

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : R p →+* κ)
    (x₁ x₂ : ↥(fibre0 (N₀ := N₀) toκ)) (h₁ : IsClosed ({x₁} : Set ↥(fibre0 (N₀ := N₀) toκ)))
    (h₂ : IsClosed ({x₂} : Set ↥(fibre0 (N₀ := N₀) toκ)))
    (h : (𝔓.comp κ toκ 1 ≫ fibreMap0 𝔓.π toκ).base x₁ = (𝔓.comp κ toκ 1 ≫ fibreMap0 𝔓.π toκ).base x₂) :
    x₁ = x₂ := by
  haveI : IsIso (𝔓.efib κ toκ) := 𝔓.efib_iso κ toκ

  have hP₁ : (inv (𝔓.efib κ toκ)).base x₁ ∈ closedPoints (𝔓.Mfib κ toκ).C :=
    ModularCurve.DRModelPackageLevel.Radicial.mem_closedPoints_inv_apply (𝔓.efib κ toκ) x₁ h₁
  have hP₂ : (inv (𝔓.efib κ toκ)).base x₂ ∈ closedPoints (𝔓.Mfib κ toκ).C :=
    ModularCurve.DRModelPackageLevel.Radicial.mem_closedPoints_inv_apply (𝔓.efib κ toκ) x₂ h₂
  obtain ⟨k₁, hk₁⟩ := 𝔓.comp1_pi_place κ toκ ⟨_, hP₁⟩
  obtain ⟨k₂, hk₂⟩ := 𝔓.comp1_pi_place κ toκ ⟨_, hP₂⟩

  have hread : ∀ y : ↥(fibre0 (N₀ := N₀) toκ),
      (𝔓.efib κ toκ ≫ 𝔓.comp κ toκ 1 ≫ fibreMap0 𝔓.π toκ).base ((inv (𝔓.efib κ toκ)).base y) =
        (𝔓.comp κ toκ 1 ≫ fibreMap0 𝔓.π toκ).base y := fun y => by
    change (𝔓.comp κ toκ 1 ≫ fibreMap0 𝔓.π toκ).base ((𝔓.efib κ toκ).base ((inv (𝔓.efib κ toκ)).base y)) = _
    rw [ModularCurve.DRModelPackageLevel.Radicial.apply_inv_apply]
  have heq : arithFrobC p κ N₀ • (𝔓.Mfib κ toκ).placeOfPoint ⟨_, hP₁⟩ =
      arithFrobC p κ N₀ • (𝔓.Mfib κ toκ).placeOfPoint ⟨_, hP₂⟩ := by
    rw [← hk₁, ← hk₂]
    congr 2
    dsimp only [Subtype.coe_mk]
    rw [hread, hread, h]
  have hPP : (⟨_, hP₁⟩ : closedPoints (𝔓.Mfib κ toκ).C) = ⟨_, hP₂⟩ :=
    (𝔓.Mfib κ toκ).placeOfPoint_bijective.1 (smul_left_cancel _ heq)
  have hx := congrArg (fun P : closedPoints (𝔓.Mfib κ toκ).C => (𝔓.efib κ toκ).base P.1) hPP
  simpa only [ModularCurve.DRModelPackageLevel.Radicial.apply_inv_apply] using hx

end S_ModularCurve_DRModelPackageLevel_eq_of_isClosed_of_comp_one_fibreMap0_pi_apply_eq
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_eq_of_isClosed_of_comp_one_fibreMap0_pi_apply_eq (solution)

-- Prove2me | solution 1 for GlobalTheory.TwistLoc.isLocalization_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:18:46.370524+00:00
-- url     : https://prove2.me/submissions/458a9073-5a49-4560-b1d6-a3807207d4aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistLoc
variable {R : Type} [CommRing R] {X Y Y' Z : Scheme.{0}}
variable {Rm : Type} [CommRing Rm] [Algebra R Rm] (M : Submonoid R) [IsLocalization M Rm]
  {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of Rm)} {h : Y' ⟶ Y}
  (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))))
include H
namespace GlobalTheory.TwistLoc
theorem _root_.solution {U : Y.Opens} (hU : IsCompact (U : Set Y)) (hU' : IsQuasiSeparated (U : Set Y)) :
    letI := (h.app U).hom.toAlgebra
    IsLocalization (M.map (cst π U).hom) Γ(Y', h ⁻¹ᵁ U) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R Rm))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat Rm M)
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := h ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU hU')
  have po' : IsPushout (cst π U) (CommRingCat.ofHom (algebraMap R Rm)) (h.app U) (cst π' (h ⁻¹ᵁ U)) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of Rm)) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [cst]
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · simp [cst]
  let := (h.app U).hom.toAlgebra
  let : Algebra R Γ(Y, U) := (cst π U).hom.toAlgebra
  let : Algebra Rm Γ(Y', h ⁻¹ᵁ U) := (cst π' (h ⁻¹ᵁ U)).hom.toAlgebra
  let : Algebra R Γ(Y', h ⁻¹ᵁ U) := (cst π U ≫ h.app U).hom.toAlgebra
  have : IsScalarTower R Γ(Y, U) Γ(Y', h ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsScalarTower R Rm Γ(Y', h ⁻¹ᵁ U) := .of_algebraMap_eq' congr($(po'.w).hom)
  exact (Algebra.isLocalization_iff_isPushout M Rm).mpr (CommRingCat.isPushout_iff_isPushout.mp po')
end GlobalTheory.TwistLoc

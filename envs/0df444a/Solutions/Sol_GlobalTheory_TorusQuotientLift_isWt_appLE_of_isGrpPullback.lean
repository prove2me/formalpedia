-- Prove2me | solution 1 for GlobalTheory.TorusQuotientLift.isWt_appLE_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:33:59.7221+00:00
-- url     : https://prove2.me/submissions/481d85f8-485c-4aa5-80a2-12f02155c28f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open GlobalTheory.UU GlobalTheory.AffineThickening
noncomputable section
open GlobalTheory GlobalTheory.TorusQuotientLift
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
variable {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'} {V : G.left.Opens} {V' : G'.left.Opens}
namespace GlobalTheory.TorusQuotientLift
theorem _root_.solution {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F)
    (hT : TorusCompat f F i' i) (h : V' ≤ F ⁻¹ᵁ V) (χ : X) (x : Γ(G.left, V)) (hx : IsWt i V x χ) :
    IsWt i' V' ((F.appLE V V' h).hom x) χ := fun Z t g h₁ h₂ => by
  obtain ⟨τ, hτ, hχ, e⟩ := hT
  let t₀ : Over.mk (Z.hom ≫ f) ⟶ splitTorus S X := Over.homMk (t.left ≫ τ) (by
    rw [Category.assoc, hτ, ← Category.assoc, Over.w]; rfl)
  let g₀ : Over.mk (Z.hom ≫ f) ⟶ G := Over.homMk (g.left ≫ F) (by
    rw [Category.assoc, hF.1.w, ← Category.assoc, Over.w]; rfl)
  have m : ((t₀ ≫ i) * g₀).left = ((t ≫ i') * g).left ≫ F := hF.2 Z (t ≫ i') g _ _
    ((Category.assoc _ _ _).trans ((congrArg (t.left ≫ ·) e).trans (Category.assoc _ _ _).symm)) rfl
  have k := hx _ t₀ g₀ (by rw [m]; exact h₁.trans (Scheme.Hom.preimage_mono _ h))
    (h₂.trans (Scheme.Hom.preimage_mono _ h))
  simp only [m] at k
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply (F.appLE V V' h), Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE, ← hχ]
  exact k
end GlobalTheory.TorusQuotientLift

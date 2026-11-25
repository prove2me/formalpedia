-- Prove2me | solution 1 for GlobalTheory.ker_app_eq_map_appLE_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:35:32.615405+00:00
-- url     : https://prove2.me/submissions/91047202-bc3e-4481-9396-0589645916a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Theorems.Thm_GlobalTheory_PrimeSection_ker_eq_map_of_isPushout
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y Z : Scheme.{0}} {A C : CommRingCat.{0}}
    {β : A ⟶ C} (hβ : Function.Surjective β) {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C}
    (h : IsPullback i f' f (Spec.map β)) {U : Y.Opens} (hU : IsAffineOpen U) :
    RingHom.ker (i.app U).hom =
      (RingHom.ker β.hom).map ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top).hom := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := i ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top) β (i.app U)
      ((Scheme.ΓSpecIso C).inv ≫ f'.appLE ⊤ (i ⁻¹ᵁ U) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  exact PrimeSection.ker_eq_map_of_isPushout hpo' hβ
end GlobalTheory

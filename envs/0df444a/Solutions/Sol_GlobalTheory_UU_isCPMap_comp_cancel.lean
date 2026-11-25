-- Prove2me | solution 1 for GlobalTheory.UU.isCPMap_comp_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:09:38.583489+00:00
-- url     : https://prove2.me/submissions/4f6d4266-49a1-456d-b290-39cbe1709b9f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapCompCancel
import Theorems.Thm_GlobalTheory_UU_IsCPMap_cancel
import Theorems.Thm_GlobalTheory_UU_IsCPMap_exists_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
namespace GlobalTheory.UU
theorem _root_.solution :
    (∀ (S S' S'' : Scheme.{0}) (f : S' ⟶ S) (f' : S'' ⟶ S') (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (G'' : Over S'') [GrpObj G''] [IsCommMonObj G''] (P : CP G) (P' : CP G') (P'' : CP G'') (F : G'.left ⟶ G.left) (hw) (w) (F' : G''.left ⟶ G'.left) (hw' : F' ≫ G'.hom = G''.hom ≫ f') (hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f), IsCPMap P' P f F hw w → (∀ w', IsCPMap P'' P' f' F' hw' w' → ∃ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' ∧ Tri w w' w'') ∧ ((∀ (T : Over S'') (x y : T ⟶ G''), toBase hw' (x * y) = toBase hw' x * toBase hw' y) → ∀ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' → ∃ w', IsCPMap P'' P' f' F' hw' w' ∧ Tri w w' w'')) := by
  intro S S' S'' f f' G _ _ G' _ _ G'' _ _ P P' P'' F hw w F' hw' hw'' h
  refine ⟨fun w' h' => ?_, fun mul w'' h'' => ?_⟩
  · obtain ⟨w'', Tw, H⟩ := h.exists_comp h' hw''
    exact ⟨w'', H, Tw⟩
  · obtain ⟨w', Tw⟩ := Geo.Tor.exists_cancel P.L.isLB w w'' ((isGen_iff _).1 h.gen) ((isGen_iff _).1 h''.gen)
      P'.L.isLB P''.L.isLB
    exact ⟨w', h.cancel h'' mul Tw, Tw⟩
end GlobalTheory.UU

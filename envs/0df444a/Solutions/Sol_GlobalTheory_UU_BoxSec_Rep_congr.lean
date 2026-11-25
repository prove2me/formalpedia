-- Prove2me | solution 1 for GlobalTheory.UU.BoxSec.Rep.congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:59:45.592659+00:00
-- url     : https://prove2.me/submissions/3acfb79b-f26d-4199-aa07-ebf2f0d13838

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RepSymInv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BoxSec
variable {S X : Scheme.{0}} (L : LB X) (Y : Over S)
variable {L Y}
namespace GlobalTheory.UU.BoxSec
namespace Rep
theorem _root_.solution {P P' v v'} (h : Rep L Y P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), P U h = P' U h)
    (hv : ∀ (T : Over S) (r : T ⟶ Y) (z : T.left) (J), Good L z J → v T r z J = v' T r z J) : Rep L Y P' v' := by
  obtain ⟨K', _, φ', ε', s', hP', hv'⟩ := h
  exact ⟨K', inferInstance, φ', ε', s', fun U _ h => (hP' U h).trans (hP U h),
    fun T r z J hJ => (hv' T r z J hJ).trans (hv T r z J hJ)⟩
end Rep
end GlobalTheory.UU.BoxSec

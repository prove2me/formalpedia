-- Prove2me | solution 1 for GlobalTheory.TorusGrading.eq_zero_of_sum_chV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:26:14.24473+00:00
-- url     : https://prove2.me/submissions/2f311206-95f5-46d8-99bf-1547c530178a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_eq_zero_of_sum


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
open GlobalTheory
open GlobalTheory.TorusGrading
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
namespace GlobalTheory.TorusGrading
theorem _root_.solution (Z : Over S) (s : Finset X) (h : X → Γ(Z.left, ⊤))
    (hs : ∑ χ ∈ s, (chV (fst (splitTorus S X) Z) χ).val * (snd (splitTorus S X) Z).left.appTop.hom (h χ) = 0) :
    ∀ χ ∈ s, h χ = 0 := by
  refine TorusInj.eq_zero_of_sum X Z s h (Eq.trans (Finset.sum_congr rfl fun χ _ => ?_) hs)
  refine congrArg₂ (· * ·) ?_ rfl
  rw [chV_val]
  exact congrArg (fun q => q.hom (TorusInj.chiP X Z χ))
    ((splitTorus S X ⊗ Z).left.presheaf.map_id (Opposite.op ⊤))
end GlobalTheory.TorusGrading

-- Prove2me | solution 1 for GlobalTheory.PowGrp.prop_of_isPowGrp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:51.052994+00:00
-- url     : https://prove2.me/submissions/520cd6ed-0a3d-4cd6-aa3f-c9cf999ee4d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SmoothIsMultiplicative
import Theorems.Thm_GlobalTheory_PowGrp_prop_powObj
import Theorems.Thm_GlobalTheory_PowGrp_exists_iso_powObj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowGrp
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
attribute [local instance] smooth_isMultiplicative
namespace GlobalTheory.PowGrp
theorem _root_.solution (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) (hG : P G.hom) : P G'.hom := by
  obtain ⟨e, he, hw⟩ := exists_iso_powObj p
  rw [hw]
  exact (P.cancel_left_of_respectsIso e _).2 (prop_powObj P G hG j)
end GlobalTheory.PowGrp

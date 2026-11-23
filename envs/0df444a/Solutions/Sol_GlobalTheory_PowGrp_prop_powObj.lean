-- Prove2me | solution 1 for GlobalTheory.PowGrp.prop_powObj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:48.607456+00:00
-- url     : https://prove2.me/submissions/8053c6f6-2280-4c0a-9456-e0684cfa4682

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SmoothIsMultiplicative

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
namespace GlobalTheory.PowGrp
theorem _root_.solution (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    (G : Over S) (hG : P G.hom) : ∀ n : ℕ, P (powObj G n).hom
  | 0 => P.id_mem S
  | n + 1 =>
    P.comp_mem (pullback.fst G.hom (powObj G n).hom) G.hom
      (P.pullback_fst _ _ (solution P G hG n)) hG
end GlobalTheory.PowGrp

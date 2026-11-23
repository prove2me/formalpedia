-- Prove2me | solution 1 for GlobalTheory.TorusToProper.pt_univ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:56.570012+00:00
-- url     : https://prove2.me/submissions/c4eba184-2629-4657-9d50-62da94d0259b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Theorems.Thm_GlobalTheory_TorusToProper_charRing_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torusIso_hom_fst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusToProper
variable {K : Type} [Field K]
variable (K) (X : Type) [AddCommGroup X]
namespace GlobalTheory.TorusToProper
theorem _root_.solution : (pt K X _ (univ K X)).left = (Rosenlicht.torusIso K X).hom := by
  apply pullback.hom_ext
  · refine (ptFun_fst K X _ _).trans (Eq.trans ?_ (Rosenlicht.torusIso_hom_fst K X).symm)
    congr 2
    apply Rosenlicht.ringHom_ext_ZU
    intro y
    rw [charRing_single]
    simp [univ]
  · exact (Over.w (pt K X _ (univ K X))).trans (Rosenlicht.torusIso_hom_hom K X).symm
end GlobalTheory.TorusToProper

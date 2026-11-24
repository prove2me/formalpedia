-- Prove2me | solution 1 for GlobalTheory.GrpTangent.isTangent_toFibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:43.560799+00:00
-- url     : https://prove2.me/submissions/e54422fe-c548-41c4-8474-2bec6e3a10b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_GrpTangent_epsZeroAt_epsBaseAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.GrpTangent.epsZeroAt_epsBaseAt

set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.GrpTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
variable {k : Type} [CommRing k] (p : Sp k ⟶ S)
namespace GlobalTheory.GrpTangent
theorem _root_.solution (w : Over.mk (dualBase k ≫ p) ⟶ G) :
    IsTangent (toFibre p w) ↔ epsZeroAt p ≫ w = 1 := by
  have e : (1 : Over.mk p ⟶ G).left = p ≫ η[G].left := by
    rw [Hom.one_def, Over.comp_left]; rfl
  constructor
  · intro h
    refine Over.OverMorphism.ext ?_
    rw [e, ← one_pullback_left_fst, ← h, Category.assoc, toFibre_left_fst]
    rfl
  · intro h
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, toFibre_left_fst, one_pullback_left_fst, ← e, ← h]
      rfl
    · rw [Category.assoc]
      exact ((congrArg (dualPt k ≫ ·) (Over.w (toFibre p w))).trans (dualPt_dualBase k)).trans
        (Over.w η[(Over.pullback p).obj G]).symm
end GlobalTheory.GrpTangent

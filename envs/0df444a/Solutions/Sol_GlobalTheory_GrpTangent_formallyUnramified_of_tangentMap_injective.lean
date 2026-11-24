-- Prove2me | solution 1 for GlobalTheory.GrpTangent.formallyUnramified_of_tangentMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:43.000819+00:00
-- url     : https://prove2.me/submissions/d44770ba-c854-41b5-97d5-01635ab701e2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_TangentCrit_formallyUnramified_of_tangent
import Theorems.Thm_GlobalTheory_GrpTangent_epsZeroAt_epsBaseAt
import Theorems.Thm_GlobalTheory_GrpTangent_eq_of_tangentMap_injective
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
namespace GlobalTheory.GrpTangent
theorem _root_.solution (f : G ⟶ H) [IsMonHom f]
    [LocallyOfFiniteType f.left]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
      Function.Injective (tangentMap ((Over.pullback p).map f))) :
    FormallyUnramified f.left := by
  refine formallyUnramified_of_tangent _ fun k _ _ w hw => ?_
  let p : Sp k ⟶ S := dualPt k ≫ w ≫ G.hom
  have hw' : w ≫ G.hom = dualBase k ≫ p := by
    have := congrArg (· ≫ H.hom) hw
    simpa [p] using this
  let w₀ : Over.mk (dualBase k ≫ p) ⟶ G := Over.homMk w hw'
  exact congrArg Over.Hom.left (eq_of_tangentMap_injective p f (h k p) w₀
    (epsBaseAt p ≫ epsZeroAt p ≫ w₀) (by rw [epsZeroAt_epsBaseAt_assoc])
    (Over.OverMorphism.ext (by simpa [w₀, epsBaseAt, epsZeroAt] using hw)))
end GlobalTheory.GrpTangent

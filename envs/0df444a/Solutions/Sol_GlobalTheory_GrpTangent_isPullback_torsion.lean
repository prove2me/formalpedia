-- Prove2me | solution 1 for GlobalTheory.GrpTangent.isPullback_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:58.681329+00:00
-- url     : https://prove2.me/submissions/b436af2e-872d-4475-819d-dd631d429782

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.GrpTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
namespace GlobalTheory.GrpTangent
theorem _root_.solution (n : ℕ) :
    IsPullback (torsion.ι G n).left (torsion G n).hom (mulN G n).left η[G].left := by
  have h := (IsPullback.of_hasPullback (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).map (Over.forget S)
  have e : (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).left = (torsion G n).hom :=
    (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)))
  exact e ▸ h
end GlobalTheory.GrpTangent

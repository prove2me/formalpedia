-- Prove2me | solution 1 for GlobalTheory.GrpTangent.epsScale_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:20.337297+00:00
-- url     : https://prove2.me/submissions/6083378e-c82b-4749-afe5-334832588bab

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
variable {R : Type} [CommRing R] {G H : Over (Sp R)} [GrpObj G] [GrpObj H]
namespace GlobalTheory.GrpTangent
theorem _root_.solution : epsScale (1 : R) = 𝟙 _ := by
  ext1
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  ext <;> simp [epsScaleR]
end GlobalTheory.GrpTangent

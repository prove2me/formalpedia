-- Prove2me | solution 1 for GlobalTheory.GrpTangent.tangentMap_pullback_mulN_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:08.503556+00:00
-- url     : https://prove2.me/submissions/78da595c-9290-4623-aea6-4df40d243469

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_GrpTangent_pullback_map_mulN
import Theorems.Thm_GlobalTheory_GrpTangent_tangentMap_mulN_bijective
import Theorems.Thm_GlobalTheory_GrpTangent_isUnit_natCast_of_point

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
theorem _root_.solution [IsCommMonObj G] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    {R : Type} [CommRing R] (p : Sp R ⟶ S) :
    Function.Bijective (tangentMap ((Over.pullback p).map (mulN G n))) := by
  convert tangentMap_mulN_bijective ((Over.pullback p).obj G) (isUnit_natCast_of_point hn p) using 2
  exact pullback_map_mulN p G n
end GlobalTheory.GrpTangent

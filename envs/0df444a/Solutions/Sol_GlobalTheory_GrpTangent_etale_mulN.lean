-- Prove2me | solution 1 for GlobalTheory.GrpTangent.etale_mulN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:34:54.549802+00:00
-- url     : https://prove2.me/submissions/baeb71c7-82dd-4d6c-8046-9bd046e1e5a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_GrpTangent_etale_of_tangentMap_bijective
import Theorems.Thm_GlobalTheory_GrpTangent_tangentMap_pullback_mulN_bijective

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
theorem _root_.solution [IsCommMonObj G] [Smooth G.hom] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) :
    Etale (mulN G n).left :=
  etale_of_tangentMap_bijective _ fun _ _ _ p => tangentMap_pullback_mulN_bijective G hn p
end GlobalTheory.GrpTangent

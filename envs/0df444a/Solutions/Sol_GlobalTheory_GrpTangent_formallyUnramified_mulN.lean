-- Prove2me | solution 1 for GlobalTheory.GrpTangent.formallyUnramified_mulN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:50:14.746114+00:00
-- url     : https://prove2.me/submissions/083f5498-5911-4240-b4ea-0790b45fe645

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_GrpTangent_formallyUnramified_of_tangentMap_injective
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
theorem _root_.solution [IsCommMonObj G] [LocallyOfFiniteType G.hom] {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) : FormallyUnramified (mulN G n).left := by
  have : LocallyOfFiniteType ((mulN G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have := locallyOfFiniteType_of_comp (mulN G n).left G.hom
  exact formallyUnramified_of_tangentMap_injective _ fun k _ _ p =>
    (tangentMap_pullback_mulN_bijective G hn p).1
end GlobalTheory.GrpTangent

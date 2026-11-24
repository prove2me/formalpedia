-- Prove2me | solution 1 for GlobalTheory.GrpTangent.etale_of_tangentMap_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:20:21.250683+00:00
-- url     : https://prove2.me/submissions/9b5b7acf-aefe-4c4d-86a5-424967f8b475

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_GrpTangent_formallyUnramified_of_tangentMap_injective
import Theorems.Thm_GlobalTheory_GrpTangent_smooth_of_tangentMap_surjective

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
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
namespace GlobalTheory.GrpTangent
theorem _root_.solution (f : G ⟶ H) [IsMonHom f] [Smooth G.hom]
    [LocallyOfFiniteType H.hom]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
      Function.Bijective (tangentMap ((Over.pullback p).map f))) :
    Etale f.left := by
  have := smooth_of_tangentMap_surjective f fun k _ _ p => (h k p).2
  have := formallyUnramified_of_tangentMap_injective f fun k _ _ p => (h k p).1
  exact Etale.of_formallyUnramified_of_flat _
end GlobalTheory.GrpTangent

-- Prove2me | solution 1 for GlobalTheory.GrpTangent.isFinite_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:55:15.673455+00:00
-- url     : https://prove2.me/submissions/27b5f76e-10c0-416c-a4d3-a6295c754715

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_GrpTangent_isPullback_torsion
import Theorems.Thm_GlobalTheory_GrpTangent_isFinite_mulN

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
theorem _root_.solution [IsCommMonObj G] [Smooth G.hom] [IsProper G.hom] {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) : IsFinite (torsion G n).hom :=
  MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_torsion G n) (isFinite_mulN G hn)
end GlobalTheory.GrpTangent

-- Prove2me | solution 1 for GlobalTheory.GrpTangent.etale_id_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:44:48.306923+00:00
-- url     : https://prove2.me/submissions/b28713a6-3153-4f95-a740-c871ecf84b3f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_GrpTangent_etale_mulN

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
    Etale (𝟙 G ^ n).left := mulN_eq_pow G n ▸ etale_mulN G hn
end GlobalTheory.GrpTangent

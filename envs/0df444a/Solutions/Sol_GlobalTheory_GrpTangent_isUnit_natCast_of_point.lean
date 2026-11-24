-- Prove2me | solution 1 for GlobalTheory.GrpTangent.isUnit_natCast_of_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:53:56.920957+00:00
-- url     : https://prove2.me/submissions/346e1698-2a40-496c-808a-833abcc51f93

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
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
namespace GlobalTheory.GrpTangent
theorem _root_.solution {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) {R : Type} [CommRing R]
    (p : Sp R ⟶ S) : IsUnit (n : R) := by
  simpa using hn.map (p.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom).hom
end GlobalTheory.GrpTangent

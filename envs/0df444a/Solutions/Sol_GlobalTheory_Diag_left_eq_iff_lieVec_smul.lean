-- Prove2me | solution 1 for GlobalTheory.Diag.left_eq_iff_lieVec_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:14:16.260881+00:00
-- url     : https://prove2.me/submissions/a7681935-ffd1-4216-aed3-31bfa2d5c183

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Theorems.Thm_GlobalTheory_Diag_left_eq_epsScaleR_iff
import Theorems.Thm_GlobalTheory_Diag_epsScaleR_base

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent IsLieComb IsLieBasis OAct epsPt
  IsLieEigen LieMult)
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.Diag
variable {R : Type} [CommRing R] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
namespace GlobalTheory.Diag
theorem _root_.solution (a : R) (c : X →+ R) (u : epsR R ⟶ splitTorus (Sp R) X) :
    u.left = spMap (epsScaleR a) ≫ (lieVec c).left ↔ u = lieVec (a • c) := left_eq_epsScaleR_iff a (epsScaleR_base a) c u
end GlobalTheory.Diag

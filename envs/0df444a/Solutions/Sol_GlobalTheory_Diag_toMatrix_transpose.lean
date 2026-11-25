-- Prove2me | solution 1 for GlobalTheory.Diag.toMatrix_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:32:35.02631+00:00
-- url     : https://prove2.me/submissions/863ef2d9-d52e-44f9-87d2-1b23ce08822a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Theorems.Thm_GlobalTheory_Diag_transpose_apply
import Theorems.Thm_GlobalTheory_Diag_dualBasis_repr
import Theorems.Thm_GlobalTheory_Diag_dualBasis_apply

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
variable {I J : Type} [Fintype I] [Fintype J]
namespace GlobalTheory.Diag
theorem _root_.solution [DecidableEq I] [DecidableEq J] (b : Module.Basis I ℤ X)
    (b' : Module.Basis J ℤ Y) (u : Y →+ X) :
    LinearMap.toMatrix (dualBasis R b) (dualBasis R b') (transpose R u) =
      ((LinearMap.toMatrix b' b u.toIntLinearMap).map (Int.castRingHom R)).transpose := by
  ext j i
  rw [LinearMap.toMatrix_apply, Matrix.transpose_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
    dualBasis_repr, transpose_apply, AddMonoidHom.comp_apply, dualBasis_apply]
  rfl
end GlobalTheory.Diag

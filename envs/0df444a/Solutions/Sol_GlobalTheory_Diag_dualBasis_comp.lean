-- Prove2me | solution 1 for GlobalTheory.Diag.dualBasis_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:34:14.299869+00:00
-- url     : https://prove2.me/submissions/8fb86472-5481-49e8-a2f8-4bcb44949963

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Theorems.Thm_GlobalTheory_Diag_dualBasis_repr
import Theorems.Thm_GlobalTheory_Diag_dualBasis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
theorem _root_.solution [DecidableEq J] (b : Module.Basis I ℤ X)
    (b' : Module.Basis J ℤ Y) (u : Y →+ X) (i : I) :
    (dualBasis R b i).comp u =
      ∑ j, (LinearMap.toMatrix b' b u.toIntLinearMap i j : R) • dualBasis R b' j := by
  conv_lhs => rw [← (dualBasis R b').sum_repr ((dualBasis R b i).comp u)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dualBasis_repr, AddMonoidHom.comp_apply, dualBasis_apply, LinearMap.toMatrix_apply]
  rfl
end GlobalTheory.Diag

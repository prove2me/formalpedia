-- Prove2me | solution 1 for GlobalTheory.Diag.left_eq_epsScaleR_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:42:59.111258+00:00
-- url     : https://prove2.me/submissions/08b386fb-b40b-4b92-b1f9-00048886c017

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul

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
variable {S : Scheme.{0}} {R : Type} [CommRing R] {g : Sp (DualNumber R) ⟶ S}
  {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
namespace GlobalTheory.Diag
theorem _root_.solution (a : R) (hg : g = spMap (epsScaleR a) ≫ g) (c : X →+ R)
    (u : Over.mk g ⟶ splitTorus S X) :
    u.left = spMap (epsScaleR a) ≫ (epsVec g c).left ↔ u = epsVec g (a • c) := by
  rw [left_eq_iff _ hg]
  constructor
  · intro h
    refine charVal_ext fun x => ?_
    rw [h, charVal_epsVec, charVal_epsVec]
    ext <;> simp [epsScaleR, mul_comm]
  · rintro rfl x
    rw [charVal_epsVec, charVal_epsVec]
    ext <;> simp [epsScaleR, mul_comm]
end GlobalTheory.Diag

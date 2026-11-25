-- Prove2me | solution 1 for GlobalTheory.Diag.epsScaleR_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:30:51.675134+00:00
-- url     : https://prove2.me/submissions/ce1205e0-07c6-4323-b035-8a6c85b14eae

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
theorem _root_.solution (a : R) :
    spMap (algebraMap R (DualNumber R)) = spMap (epsScaleR a) ≫ spMap (algebraMap R (DualNumber R)) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
end GlobalTheory.Diag

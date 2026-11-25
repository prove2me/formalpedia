-- Prove2me | solution 1 for GlobalTheory.Diag.dualBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:53:00.578188+00:00
-- url     : https://prove2.me/submissions/7529ff2c-26e9-4a24-ada6-0a78d67a5ed3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Theorems.Thm_GlobalTheory_Diag_dualBasis_repr
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
theorem _root_.solution (b : Module.Basis I ℤ X) (i : I) (x : X) :
    dualBasis R b i x = (b.repr x i : R) := by
  have key : ∀ j, dualBasis R b i (b j) = (b.repr (b j) i : R) := by
    intro j
    rw [← dualBasis_repr, Module.Basis.repr_self, Module.Basis.repr_self]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  have e : (dualBasis R b i).toIntLinearMap = (Int.castAddHom R).toIntLinearMap.comp (b.coord i) :=
    b.ext fun j => by simpa using key j
  simpa using congrArg (fun f => f x) e
end GlobalTheory.Diag

-- Prove2me | solution 1 for GlobalTheory.TangentPow.pow_eq_scale_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:34.595181+00:00
-- url     : https://prove2.me/submissions/d94a7c7b-4dda-422f-bd78-67d4d589ca2c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Theorems.Thm_GlobalTheory_TangentPow_scale_one
import Theorems.Thm_GlobalTheory_TangentPow_scale_zero_comp
import Theorems.Thm_GlobalTheory_TangentPow_scale_add_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.TangentPow
variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]
variable {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {y : specO O (DualNumber R) ⟶ G}
namespace GlobalTheory.TangentPow
theorem _root_.solution (hy : ptMap (TrivSqZeroExt.fstHom O R R) ≫ y = 1) (N : ℕ) :
    y ^ N = scale O (N : R) ≫ y := by
  induction N with
  | zero => rw [pow_zero, Nat.cast_zero, scale_zero_comp hy]
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, scale_add_comp hy, ih, scale_one, Category.id_comp]
end GlobalTheory.TangentPow

-- Prove2me | solution 1 for GlobalTheory.TangentPow.ofTwo_toTwo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:46:37.007876+00:00
-- url     : https://prove2.me/submissions/e058f8cb-bf58-49c2-86b4-6b132a13c174

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Theorems.Thm_GlobalTheory_TangentPow_ptMap_comp_ptMap
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.TangentPow
variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]
namespace GlobalTheory.TangentPow
theorem _root_.solution (l : R →ₗ[R] R × R) (l' : R × R →ₗ[R] R) :
    ofTwo O l' ≫ toTwo O l = scale O (l' (l 1)) := by
  rw [ofTwo, toTwo, ptMap_comp_ptMap, scale]
  congr 1
  refine AlgHom.ext fun x => ?_
  have : l' (l x.snd) = l' (l 1) * x.snd := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
  ext <;> simp [this]
end GlobalTheory.TangentPow

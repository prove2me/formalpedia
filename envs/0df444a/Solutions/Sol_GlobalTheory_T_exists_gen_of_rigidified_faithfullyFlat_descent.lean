-- Prove2me | solution 1 for GlobalTheory.T.exists_gen_of_rigidified_faithfullyFlat_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:15:07.151987+00:00
-- url     : https://prove2.me/submissions/7ccd4120-53d5-483c-9aab-464a5524ac6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigidifiedFaithfullyFlatDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigidifiedFaithfullyFlatDescentStatement
import Theorems.Thm_GlobalTheory_exists_gen_of_rigidified_of_flat_baseChange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : Out.GlobalFnsSt → ∀ (S S' : Scheme.{0}) (π : S' ⟶ S) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Flat π → Surjective π → QuasiCompact π → (∃ t : (N.pull (eSec A)).Gen, t.IsGen) → (∃ t : (N.pull (pullback.fst A.hom π)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  first | exact @GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange | exact GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange | (intros; apply GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange <;> assumption)
end _root_.GlobalTheory.T

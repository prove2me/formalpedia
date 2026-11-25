-- Prove2me | solution 1 for GlobalTheory.AbLaw.SecOnR.isScalarTower_of_algebraMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:16.878256+00:00
-- url     : https://prove2.me/submissions/0c370677-9f97-4b32-954d-04fb10e05f2b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_smul_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
open GlobalTheory.AbLaw.SecOnR
variable (f : X ⟶ Spec (CommRingCat.of R)) {L M H : LB X} {V W : X.Opens}
namespace GlobalTheory.AbLaw.SecOnR
theorem _root_.solution [Algebra R Γ(X, V)] (h : algebraMap R Γ(X, V) = cst f V) :
    IsScalarTower R Γ(X, V) (SecOnR f M V) :=
  ⟨fun r a s => by rw [Algebra.smul_def, h, mul_smul, smul_def]⟩
end GlobalTheory.AbLaw.SecOnR

-- Prove2me | solution 1 for GlobalTheory.KS.ex_add_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:34.390409+00:00
-- url     : https://prove2.me/submissions/9d84a982-56ab-464b-909d-e4ae83f9fdba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassIsSymmOfLift

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
namespace GlobalTheory.KS
theorem _root_.solution (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
end GlobalTheory.KS

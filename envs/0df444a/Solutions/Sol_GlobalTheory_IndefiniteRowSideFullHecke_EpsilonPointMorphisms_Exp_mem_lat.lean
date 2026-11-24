-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Exp.mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:38.90834+00:00
-- url     : https://prove2.me/submissions/b663827b-00b5-4412-a8df-4ff867739f1b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_ExponentialDifferential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms
open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Exp
variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (E : Exp A g)
namespace GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Exp
theorem _root_.solution (z : Fin g → ℂ) : z ∈ E.lat ↔ E.exp z = 1 := Iff.rfl
end GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Exp

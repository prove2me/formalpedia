-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Exp.exp_add_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:56:15.259088+00:00
-- url     : https://prove2.me/submissions/c33e501d-4aeb-4d46-9264-a6dd8b11bb17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_ExponentialDifferential
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EpsilonPointMorphisms_Exp_mem_lat

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
theorem _root_.solution (z : Fin g → ℂ) (la : E.lat) : E.exp (z + la) = E.exp z := by
  rw [E.exp_add, (E.mem_lat la).1 la.2, _root_.mul_one]
end GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Exp

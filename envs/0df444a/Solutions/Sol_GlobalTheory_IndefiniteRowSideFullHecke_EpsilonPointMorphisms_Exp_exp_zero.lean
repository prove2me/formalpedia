-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Exp.exp_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:53:33.699801+00:00
-- url     : https://prove2.me/submissions/be432b6f-5ee2-49b1-99b0-834a33d27f99

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
theorem _root_.solution : E.exp 0 = 1 := E.hom.map_one
end GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Exp

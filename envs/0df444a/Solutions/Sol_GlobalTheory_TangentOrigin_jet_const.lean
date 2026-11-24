-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.jet_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:40:10.261852+00:00
-- url     : https://prove2.me/submissions/06876848-7d4a-4add-a111-03826d0da180

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Theorems.Thm_GlobalTheory_TangentOrigin_jet_snd
import Theorems.Thm_GlobalTheory_TangentOrigin_evalPt_ex_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.TangentOrigin
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.TangentOrigin
theorem _root_.solution (w : Fin g → ℂ) (W : A.left.Opens) (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) (a : ℂ) :
    jet u w W h (constFn A.hom W a) = algebraMap ℂ (DualNumber ℂ) a := by
  refine TrivSqZeroExt.ext (evalPt_ex_const u 0 h a) ?_
  rw [jet_snd, fderiv_val_const u h]
  rfl
end GlobalTheory.TangentOrigin

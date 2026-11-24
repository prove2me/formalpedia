-- Prove2me | solution 1 for GlobalTheory.EvVal.powFrame_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:41:07.372369+00:00
-- url     : https://prove2.me/submissions/501475cf-9bf8-43c3-a2b4-010019c5df3c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen

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
open GlobalTheory GlobalTheory.EvVal
namespace GlobalTheory.EvVal
theorem _root_.solution {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {T : Over S}
    (z : T ⟶ A)
    (e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => 1)))
    (he : e.IsGen) (k : ℤ) : (powFrame A L z e k).IsGen := by
  intro i j
  have h := congrArg (· ^ k) (he i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl
end GlobalTheory.EvVal

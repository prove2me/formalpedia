-- Prove2me | solution 1 for GlobalTheory.ThetaFn.exAt_translT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:40:48.154168+00:00
-- url     : https://prove2.me/submissions/6dc8e4c0-4014-4f0e-bb43-8aacea5d93f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter AppellHumbertTrivial
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {p}
namespace GlobalTheory.ThetaFn
theorem _root_.solution {y : T ⟶ A} {x : Fin g → ℂ} (hy : p ≫ y = u.ex x) (z : Fin g → ℂ) :
    exAt u p z ≫ (translT A y).left = exAt u p (z + x) := by
  have h : lift p (u.ex z) ≫ translPt A y = u.ex (z + x) := by
    unfold translPt
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd, hy, ← Hom.mul_def, ← u.ex_add, add_comm]
  have h' : lift p (u.ex z) ≫ translT A y = lift p (u.ex (z + x)) := by
    unfold translT
    rw [comp_lift, lift_fst, h]
  unfold exAt
  rw [← Over.comp_left, h']
end GlobalTheory.ThetaFn

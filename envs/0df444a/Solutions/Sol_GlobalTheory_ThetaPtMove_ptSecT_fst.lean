-- Prove2me | solution 1 for GlobalTheory.ThetaPtMove.ptSecT_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:35:47.308602+00:00
-- url     : https://prove2.me/submissions/c16d2726-f700-4a53-ac38-d4e341054324

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaPtMove
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {n : ℤ} {T : Over S}
  {s : LB.Sec (LPow A L n T)} {x : T ⟶ A}
  {ρ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => n))} {c : Γ(T.left, ⊤)}
omit [GrpObj A]
namespace GlobalTheory.ThetaPtMove
theorem _root_.solution (x : T ⟶ A) : (ptSecT A x).left ≫ (fst T A).left = 𝟙 _ := by
  rw [← Over.comp_left, ptSecT, lift_fst, Over.id_left]
end GlobalTheory.ThetaPtMove

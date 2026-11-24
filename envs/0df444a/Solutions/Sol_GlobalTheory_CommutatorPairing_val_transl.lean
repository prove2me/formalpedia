-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.val_transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:16:02.415238+00:00
-- url     : https://prove2.me/submissions/d8796fc7-b108-4581-b4d4-4d9e370bb7ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_GlobalTheory_CommutatorPairing_lift_translT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution {T Z : Over S} (θ : ThetaGrp A L k T) (x : T ⟶ A) (t : Z ⟶ T) (a : Z ⟶ A) {z : Z.left} {J}
    (hJ : Good L z J) :
    val (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (translT A x).left)
      (lift t a).left z J = thetaVal θ t ((t ≫ x) * a) z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, lift_translT]; rfl
end GlobalTheory.CommutatorPairing

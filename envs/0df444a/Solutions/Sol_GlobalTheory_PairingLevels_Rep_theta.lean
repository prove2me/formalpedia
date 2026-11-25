-- Prove2me | solution 1 for GlobalTheory.PairingLevels.Rep.theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:14:07.31965+00:00
-- url     : https://prove2.me/submissions/b286faf5-c648-4e34-8df4-6c512452d4ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq
import Theorems.Thm_GlobalTheory_CommutatorPairing_prod_theta
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
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
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLevels
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left)
variable {L} {Y : Over S} {D D' : FreeAbelianGroup (Y.left ⟶ A.left)} {f f' : ValFam L Y}
namespace GlobalTheory.PairingLevels
namespace Rep
theorem _root_.solution {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (s : Y ⟶ T) (a : Y ⟶ A) :
    Rep L (k • pt a - k • pt ((s ≫ θ.pt) * a)) (fun Z r z J => thetaVal θ (r ≫ s) (r ≫ a) z J) := by
  refine ⟨Fin 2, inferInstance, _, _, LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ
    (lift s a).left, DVR.pullGen_isGen _ _ _ _ θ.isGen _, ?_, fun Z r z J hJ => ?_⟩
  · have := congrArg Multiplicative.toAdd
      (prod_theta (k := k) θ.pt s a (fun q => Multiplicative.ofAdd (FreeAbelianGroup.of q)))
    simp only [toAdd_prod, toAdd_zpow, toAdd_ofAdd, toAdd_mul] at this
    rw [this, neg_smul, ← sub_eq_add_neg]; rfl
  · refine (val_pull hJ _ _ _).trans ?_
    rw [← Over.comp_left, comp_lift]; rfl
end Rep
end GlobalTheory.PairingLevels

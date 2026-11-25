-- Prove2me | solution 1 for GlobalTheory.PairingLevels.Rep.cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:13:08.975595+00:00
-- url     : https://prove2.me/submissions/943e5c9f-e5ed-4078-a3a1-fc146129b4ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
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
theorem _root_.solution [IsCommMonObj A] {t : LB.Gen (Theta A L)} (ht : t.IsGen) (a b c : Y ⟶ A) :
    Rep L (pt (a * b * c) - pt (a * b) - pt (a * c) - pt (b * c) + pt a + pt b + pt c - pt (1 : Y ⟶ A))
      (fun Z r z J => cubeVal t z J (r ≫ a) (r ≫ b) (r ≫ c)) := by
  refine ⟨thK, inferInstance, _, _, LB.pullGen L (thφ A (x3 A)) thε t (lift a (lift b c)).left,
    DVR.pullGen_isGen _ _ _ _ ht _, ?_, fun Z r z J hJ => ?_⟩
  · have := congrArg Multiplicative.toAdd
      (prod_cub a b c (fun q => Multiplicative.ofAdd (FreeAbelianGroup.of q)))
    simp only [toAdd_prod, toAdd_zpow, toAdd_ofAdd, toAdd_mul, toAdd_inv] at this
    rw [this]; simp only [sub_eq_add_neg]; rfl
  · refine (val_pull hJ _ _ _).trans ?_
    rw [← Over.comp_left, comp_lift, comp_lift]; rfl
end Rep
end GlobalTheory.PairingLevels

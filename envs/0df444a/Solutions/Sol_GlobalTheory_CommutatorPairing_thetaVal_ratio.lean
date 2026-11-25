-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.thetaVal_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:32:38.557575+00:00
-- url     : https://prove2.me/submissions/dccce9ee-4c17-43f4-b7b6-255fac86fd50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_GlobalTheory_CommutatorPairing_exists_ratio
import Theorems.Thm_GlobalTheory_CommutatorPairing_surj_fst
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
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T T' Z : Over S}
    (θ : ThetaGrp A L k T) (θ' : ThetaGrp A L k T') (t : Z ⟶ T) (t' : Z ⟶ T') (h : t ≫ θ.pt = t' ≫ θ'.pt)
    (z : Z.left) : ∃ u : (Z.left.presheaf.stalk z)ˣ, ∀ (a : Z ⟶ A) (J), Good L z J →
      thetaVal θ t a z J = thetaVal θ' t' a z J * u := by
  obtain ⟨c, hc⟩ := exists_ratio hL (fun U _ g => by
      refine (prod_theta θ.pt (fst Z A ≫ t) (snd Z A) g).trans
        (Eq.trans ?_ (prod_theta θ'.pt (fst Z A ≫ t') (snd Z A) g).symm)
      rw [Category.assoc, Category.assoc, h]) (fst Z A).left (lift (𝟙 Z) 1).left
      (by rw [← Over.comp_left, lift_fst]; rfl) (surj_fst hG hA Z)
    (DVR.pullGen_isGen _ _ _ _ θ.isGen (lift (fst Z A ≫ t) (snd Z A)).left)
    (DVR.pullGen_isGen _ _ _ _ θ'.isGen (lift (fst Z A ≫ t') (snd Z A)).left)
  refine ⟨gm (𝟙 _) z ⊤ c, fun a J hJ => ?_⟩
  have := (val_pull hJ _ _ _).symm.trans ((hc _ (lift (𝟙 Z) a).left z J hJ).trans
    (congrArg (· * _) (val_pull hJ _ _ _)))
  rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift,
    lift_fst_assoc, lift_fst_assoc, lift_snd, lift_fst, Category.id_comp, Category.id_comp] at this
  exact this
end GlobalTheory.CommutatorPairing

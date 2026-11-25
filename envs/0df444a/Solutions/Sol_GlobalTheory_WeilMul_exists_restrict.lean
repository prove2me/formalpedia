-- Prove2me | solution 1 for GlobalTheory.WeilMul.exists_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:54.3544+00:00
-- url     : https://prove2.me/submissions/1c630bf8-4f0d-46c9-8a93-8f5a910595f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Theorems.Thm_GlobalTheory_WeilMul_prod_theta
import Theorems.Thm_GlobalTheory_WeilMul_prod_theta_id
import Theorems.Thm_GlobalTheory_WeilMul_val_pull_tv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen


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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilMul
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.WeilMul
theorem _root_.solution (hL : L.IsLB) {T T₁ : Over S} (θ : ThetaGrp A L k T) (f : T₁ ⟶ T) :
    ∃ θ₁ : ThetaGrp A L k T₁, θ₁.pt = f ≫ θ.pt ∧ ∀ (T' : Over S) (t : T' ⟶ T₁) (a : T' ⟶ A) (z : T'.left) (J),
      Good L z J → tv θ₁ t a z J = tv θ (t ≫ f) a z J := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(snd T₁ A).left, (translPt A (f ≫ θ.pt)).left])
    (ε' := ![k, -k]) (fun U _ h => by
      refine (prod_theta θ.pt (fst T₁ A ≫ f) (snd T₁ A) h).trans ?_
      rw [prod_theta_id, Category.assoc])
    (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ
      (lift (fst T₁ A ≫ f) (snd T₁ A)).left) (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
  refine ⟨⟨f ≫ θ.pt, u, hu⟩, rfl, fun T' t a z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_pull_tv θ _ _ (lift t a) hJ).trans ?_)
  rw [lift_fst_assoc, lift_snd]
end GlobalTheory.WeilMul

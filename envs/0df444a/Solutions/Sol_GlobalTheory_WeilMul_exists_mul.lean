-- Prove2me | solution 1 for GlobalTheory.WeilMul.exists_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:34.548273+00:00
-- url     : https://prove2.me/submissions/0f932f9a-300d-48a5-94bc-ed6453aef037

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Theorems.Thm_GlobalTheory_WeilMul_prod_theta
import Theorems.Thm_GlobalTheory_WeilMul_prod_theta_id
import Theorems.Thm_GlobalTheory_WeilMul_val_pull_tv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
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
theorem _root_.solution [IsCommMonObj A] (hL : L.IsLB) {T : Over S} (θ θ' : ThetaGrp A L k T) :
    ∃ θ₁ : ThetaGrp A L k T, θ₁.pt = θ.pt * θ'.pt ∧ ∀ (T' : Over S) (t : T' ⟶ T) (a : T' ⟶ A) (z : T'.left) (J),
      Good L z J → tv θ₁ t a z J = tv θ t a z J * tv θ' t ((t ≫ θ.pt) * a) z J := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(snd T A).left, (translPt A (θ.pt * θ'.pt)).left])
    (ε' := ![k, -k]) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_theta_id θ.pt h)
        (prod_theta θ'.pt (fst T A) ((fst T A ≫ θ.pt) * snd T A) h))).trans ?_
      rw [prod_theta_id, MonObj.comp_mul, mul_comm (fst T A ≫ θ.pt) (fst T A ≫ θ'.pt),
        _root_.mul_assoc (fst T A ≫ θ'.pt)]
      simp only [zpow_neg, _root_.mul_assoc, inv_mul_cancel_left])
    (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ'.pt).left] ![k, -k] θ'.φ
      (lift (fst T A) ((fst T A ≫ θ.pt) * snd T A)).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ θ.isGen (DVR.pullGen_isGen _ _ _ _ θ'.isGen _))
  refine ⟨⟨θ.pt * θ'.pt, u, hu⟩, rfl, fun T' t a z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    ((val_pull_tv θ' _ _ (lift t a) hJ).trans ?_)))
  rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, lift_fst]
end GlobalTheory.WeilMul

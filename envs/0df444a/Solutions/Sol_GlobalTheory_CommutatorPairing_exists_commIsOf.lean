-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.exists_commIsOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:32:14.16883+00:00
-- url     : https://prove2.me/submissions/39558159-7093-4966-9f5f-b94da1ae8212

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_GlobalTheory_CommutatorPairing_exists_ratio
import Theorems.Thm_GlobalTheory_CommutatorPairing_surj_fst
import Theorems.Thm_GlobalTheory_CommutatorPairing_prod_theta
import Theorems.Thm_GlobalTheory_CommutatorPairing_val_prod
import Theorems.Thm_GlobalTheory_CommutatorPairing_commIsOf_iff
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm


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
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    (θx θy : ThetaGrp A L k T) : ∃ c : Γ(T.left, ⊤)ˣ, CommIsOf A L k θx θy c := by
  have := hA.comm
  have p₁ : ∀ (x : T ⟶ A) (U : Type) [CommGroup U] (g : ((T ⊗ A).left ⟶ A.left) → U),
      ∏ i : Fin 2, g (![(snd T A).left, (translPt A x).left] i) ^ ![k, -k] i =
        g (snd T A).left ^ k * g ((fst T A ≫ x) * snd T A).left ^ (-k) := fun x U _ g => by
    rw [Fin.prod_univ_two]; rfl
  obtain ⟨c, hc⟩ := exists_ratio hL (fun U _ g => by
      refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (p₁ θx.pt U g)
        (prod_theta θy.pt (fst T A) ((fst T A ≫ θx.pt) * snd T A) g)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (p₁ θy.pt U g)
          (prod_theta θx.pt (fst T A) ((fst T A ≫ θy.pt) * snd T A) g)).symm)
      rw [mul_left_comm (fst T A ≫ θy.pt)]
      simp only [zpow_neg, _root_.mul_assoc, inv_mul_cancel_left]) (fst T A).left (lift (𝟙 T) 1).left
      (by rw [← Over.comp_left, lift_fst]; rfl) (surj_fst hG hA T)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ θx.isGen (DVR.pullGen_isGen _ _ _ _ θy.isGen (translT A θx.pt).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ θy.isGen (DVR.pullGen_isGen _ _ _ _ θx.isGen (translT A θy.pt).left))
  refine ⟨c, (commIsOf_iff hL θx θy c).2 fun Z t a z J hJ => ?_⟩
  have := (val_prod θx θy t a hJ).symm.trans ((hc _ (lift t a).left z J hJ).trans
    (congrArg (· * _) (val_prod θy θx t a hJ)))
  rw [← Over.comp_left, lift_fst] at this
  exact mul_inv_eq_iff_eq_mul.2 (this.trans (mul_comm _ _))
end GlobalTheory.CommutatorPairing

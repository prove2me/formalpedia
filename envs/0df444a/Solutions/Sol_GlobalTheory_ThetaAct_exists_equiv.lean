-- Prove2me | solution 1 for GlobalTheory.ThetaAct.exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:33:35.588942+00:00
-- url     : https://prove2.me/submissions/9039d2e1-ab53-4307-8cf4-ea4fa9a80635

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Theorems.Thm_GlobalTheory_ThetaAct_sv_ext
import Theorems.Thm_GlobalTheory_ThetaAct_translT_translT
import Theorems.Thm_GlobalTheory_ThetaAct_translT_one
import Theorems.Thm_GlobalTheory_ThetaAct_exists_lin
import Theorems.Thm_GlobalTheory_ThetaAct_exists_inv

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaAct
open GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
namespace GlobalTheory.ThetaAct
theorem _root_.solution (hL : L.IsLB) (θ : ThetaGrp A L k T) :
    ∃ f : SecM A L k T ≃ₗ[Γ(T.left, ⊤)] SecM A L k T, ∀ v (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → sv (f v) r z J = (tval θ r z J).val * sv v (r ≫ (translT A θ.pt).left) z J := by
  obtain ⟨θ', hp, hv⟩ := exists_inv hL θ
  obtain ⟨f, hf⟩ := exists_lin hL θ
  obtain ⟨g, hg⟩ := exists_lin hL θ'
  refine ⟨LinearEquiv.ofLinear f g (LinearMap.ext fun v => sv_ext hL fun y J hJ => ?_)
    (LinearMap.ext fun v => sv_ext hL fun y J hJ => ?_), hf⟩
  · show sv (f (g v)) _ y J = sv v _ y J
    rw [hf _ _ _ _ _ hJ, hg _ _ _ _ _ hJ, hv _ _ _ _ hJ, hp, Category.assoc, translT_translT, inv_mul_cancel,
      translT_one, Category.comp_id, Units.mul_inv_cancel_left]
  · show sv (g (f v)) _ y J = sv v _ y J
    rw [hg _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, hv _ _ _ _ hJ, hp, Category.assoc, translT_translT, mul_inv_cancel,
      translT_one, Category.comp_id, Units.inv_mul_cancel_left]
end GlobalTheory.ThetaAct

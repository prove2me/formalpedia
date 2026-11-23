-- Prove2me | solution 1 for GlobalTheory.ThetaAct.exists_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:30.712443+00:00
-- url     : https://prove2.me/submissions/2eccb0c5-9932-4e53-857b-8b62ddebe0d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Theorems.Thm_GlobalTheory_ThetaAct_sv_ext
import Theorems.Thm_GlobalTheory_ThetaAct_sv_add
import Theorems.Thm_GlobalTheory_ThetaAct_sv_smul
import Theorems.Thm_GlobalTheory_ThetaAct_exists_act
import Theorems.Thm_GlobalTheory_CommPairing_translT_fst


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
    ∃ f : SecM A L k T →ₗ[Γ(T.left, ⊤)] SecM A L k T, ∀ v (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → sv (f v) r z J = (tval θ r z J).val * sv v (r ≫ (translT A θ.pt).left) z J := by
  choose f hf using exists_act hL θ
  refine ⟨⟨⟨f, fun v w => sv_ext hL fun y J hJ => ?_⟩, fun c v => sv_ext hL fun y J hJ => ?_⟩, hf⟩
  · rw [sv_add _ _ _ _ hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, sv_add _ _ _ _ hJ, mul_add]
  · show sv (f (c • v)) _ y J = sv (c • f v) _ y J
    rw [sv_smul _ (f v) _ _ hJ, hf (c • v) _ _ _ _ hJ, hf v _ _ _ _ hJ, sv_smul _ v _ _ hJ,
      Category.assoc, translT_fst, mul_left_comm]
end GlobalTheory.ThetaAct

-- Prove2me | solution 1 for GlobalTheory.SymLiftOdd.exists_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:27:07.413449+00:00
-- url     : https://prove2.me/submissions/4b5fc03f-9fe2-42d5-9c31-64308581f721

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Theorems.Thm_GlobalTheory_SymLiftOdd_isGen_of_gm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
open GlobalTheory GlobalTheory.SymLiftOdd
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}
variable {T : Over S} {k : ℤ}
namespace GlobalTheory.SymLiftOdd
theorem _root_.solution (hL : L.IsLB) (θ : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) :
    ∃ θ' : ThetaGrp A L k T, θ'.pt = θ.pt ∧ ∀ y J, Good L y J → ∀ m,
      thetaVal θ' y J m = thetaVal θ y J m * gm (fst T A).left y ⊤ c := by
  have vc : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (j : PEmpty → L.ι),
      gm r z (LB.wchart L PEmpty.elim j) ((constGen A L c).s j) = gm (r ≫ (fst T A).left) z ⊤ c := fun r z j =>
    (gm_res r z _ (Set.mem_iInter.2 fun k => k.elim) _).trans (gm_pull r _ z ⊤ trivial c)
  have hc : (constGen A L c).IsGen := isGen_of_gm fun y j j' _ _ => by
    rw [vc, vc, trF, Fintype.prod_empty, _root_.one_mul]
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A θ.pt).left]) (ε' := ![k, -k])
    (fun U _ h => (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) rfl (Finset.prod_eq_one fun (i : PEmpty) _ => i.elim)).trans
      (_root_.mul_one _)))
    (LB.mulGen L ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] _ _ θ.φ (constGen A L c))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ θ.isGen hc)
  refine ⟨⟨θ.pt, t, ht⟩, rfl, fun y J hJ m => (hv _ _ y J hJ).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl ((vc _ y _).trans ?_)))⟩
  rw [← Over.comp_left, lift_fst]
end GlobalTheory.SymLiftOdd

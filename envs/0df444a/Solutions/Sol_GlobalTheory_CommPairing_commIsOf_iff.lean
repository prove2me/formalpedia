-- Prove2me | solution 1 for GlobalTheory.CommPairing.commIsOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:34.825595+00:00
-- url     : https://prove2.me/submissions/652d9292-f858-4433-966f-a75f1810da71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_val_constGen


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
open GlobalTheory GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommPairing
theorem _root_.solution (hL : L.IsLB) {T : Over S} (θx θy : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) :
    CommIsOf A L k θx θy c ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval θx r z J * tval θy (r ≫ (translT A θx.pt).left) z J =
        tval θy r z J * tval θx (r ≫ (translT A θy.pt).left) z J * gm (r ≫ (fst T A).left) z ⊤ c := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → ∀ θ θ' : ThetaGrp A L k T,
      val (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L _ _ θ'.φ (translT A θ.pt).left)) r z J =
        tval θ r z J * tval θ' (r ≫ (translT A θ.pt).left) z J := fun Z r z J hJ θ θ' =>
    (val_mul hJ _ _ _).trans (congrArg (tval θ r z J * ·) (val_pull hJ _ _ _))
  constructor
  · intro H Z r z J hJ
    exact (key Z r z J hJ θx θy).symm.trans ((val_corr hJ H r).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (key Z r z J hJ θy θx) (H1.val_constGen L c r z J))))
  · intro H
    refine corr_of_val hL fun y J hJ => ?_
    exact (key _ _ y J hJ θx θy).trans ((H _ _ y J hJ).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (key _ _ y J hJ θy θx) (H1.val_constGen L c _ y J))).symm)
end GlobalTheory.CommPairing

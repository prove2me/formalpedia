-- Prove2me | solution 1 for GlobalTheory.SymLiftOdd.gm_powGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:49.800294+00:00
-- url     : https://prove2.me/submissions/a3f5934a-8325-4af8-b82c-c8c3cf652265

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
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
theorem _root_.solution (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (j : Fin n × Fin 2 → L.ι) (hj : r z ∈ LB.wchart L (powφ A θ.pt n) j) :
    gm r z (LB.wchart L (powφ A θ.pt n) j) ((powGen A L k θ n).s j) =
      ∏ j₀ : Fin n, gm r z (LB.wchart L (fun b => (translT A (θ.pt ^ (j₀ : ℕ))).left ≫
            (![(snd T A).left, (translPt A θ.pt).left] b)) (fun b => j (j₀, b)))
        ((LB.pullGen L ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ
          (translT A (θ.pt ^ (j₀ : ℕ))).left).s (fun b => j (j₀, b))) := by
  unfold powGen
  refine (map_prod (gm r z (LB.wchart L (powφ A θ.pt n) j)) _ (Finset.univ : Finset (Fin n))).trans
    (Finset.prod_congr rfl fun j₀ _ => ?_)
  exact gm_res r z (V := LB.wchart L (powφ A θ.pt n) j) _ hj _
end GlobalTheory.SymLiftOdd

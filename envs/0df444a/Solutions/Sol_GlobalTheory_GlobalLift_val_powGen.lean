-- Prove2me | solution 1 for GlobalTheory.GlobalLift.val_powGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:33.595084+00:00
-- url     : https://prove2.me/submissions/e28d0b1b-6b06-4d75-b889-7fb500011056

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GlobalLift
open CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.GlobalLift
theorem _root_.solution {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) {z : Z} {J}
    (hJ : Good L z J) :
    val (powGen A L k θ n) r z J = ∏ i : Fin n, tval θ (r ≫ (translT A (θ.pt ^ (i : ℕ))).left) z J := by
  refine Eq.trans (map_prod (gm r z (LB.wchart L (powφ A θ.pt n) fun b => J (r ≫ powφ A θ.pt n b))) _
    (Finset.univ : Finset (Fin n))) ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (gm_res r z _ (hJ.mem (powφ A θ.pt n) r) _).trans (val_pull hJ
    (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ _ r)
end GlobalTheory.GlobalLift

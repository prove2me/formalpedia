-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.val_thetaPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:32:53.32817+00:00
-- url     : https://prove2.me/submissions/d2f8d2d5-7896-46f3-aa4d-4a84003bb12e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
namespace GlobalTheory.TorsionFixedAut
theorem _root_.solution {k : ℤ} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) : val (powGen A L k θ n) r z J = ∏ j : Fin n,
      thetaVal θ.φ
        (r ≫ (translT A (θ.pt ^ (j : ℕ))).left) z J := by
  unfold val powGen
  dsimp only
  refine (map_prod (gm r z _) _ Finset.univ).trans (Finset.prod_congr rfl fun j _ => ?_)
  exact (gm_res r z _ (hJ.mem (powφ A θ.pt n) r) _).trans
    (val_pull hJ (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
      (translT A (θ.pt ^ (j : ℕ))).left r)
end GlobalTheory.TorsionFixedAut

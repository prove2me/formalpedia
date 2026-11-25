-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.exists_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:07:26.744679+00:00
-- url     : https://prove2.me/submissions/73bfad39-2efe-42ca-bb6c-94c0392379fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_GlobalTheory_CommutatorPairing_prod_theta
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
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution (hL : L.IsLB) {T T' : Over S} (θ : ThetaGrp A L k T) (t : T' ⟶ T) :
    ∃ θ' : ThetaGrp A L k T', θ'.pt = t ≫ θ.pt := by
  obtain ⟨u, hu, -⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(snd T' A).left, (translPt A (t ≫ θ.pt)).left])
    (ε' := ![k, -k]) (fun U _ h => by
      refine (prod_theta θ.pt (fst T' A ≫ t) (snd T' A) h).trans ?_
      rw [Fin.prod_univ_two, Category.assoc]; rfl)
    (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ
      (lift (fst T' A ≫ t) (snd T' A)).left) (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
  exact ⟨⟨t ≫ θ.pt, u, hu⟩, rfl⟩
end GlobalTheory.CommutatorPairing

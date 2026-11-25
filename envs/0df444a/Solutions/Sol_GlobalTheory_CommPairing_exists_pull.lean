-- Prove2me | solution 1 for GlobalTheory.CommPairing.exists_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:07:21.804467+00:00
-- url     : https://prove2.me/submissions/f0d012c0-9a11-42c9-a0c0-36e3278952a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Theorems.Thm_GlobalTheory_CommPairing_whisker_translPt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommPairing
theorem _root_.solution (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T) (θ : ThetaGrp A L k T) :
    ∃ θ' : ThetaGrp A L k T', θ'.pt = h ≫ θ.pt ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J),
      Good L z J → tval θ' r z J = tval θ (r ≫ (h ▷ A).left) z J := by
  have e₀ : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  have e₁ : (h ▷ A).left ≫ (translPt A θ.pt).left = (translPt A (h ≫ θ.pt)).left := by
    rw [← Over.comp_left, whisker_translPt]
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T' A).left, (translPt A (h ≫ θ.pt)).left]) (ε' := ![k, -k])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ k) e₀
      · exact congrArg (fun q => f q ^ (-k)) e₁)
    (LB.pullGen L ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (h ▷ A).left)
    (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
  exact ⟨⟨h ≫ θ.pt, t, ht⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩
end GlobalTheory.CommPairing

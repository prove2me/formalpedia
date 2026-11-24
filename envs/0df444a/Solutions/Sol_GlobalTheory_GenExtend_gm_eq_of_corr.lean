-- Prove2me | solution 1 for GlobalTheory.GenExtend.gm_eq_of_corr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:20:45.42881+00:00
-- url     : https://prove2.me/submissions/6d212cb7-bdb6-448f-a31e-cfbc9b4ed0d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenExtend
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DvrModel
namespace GlobalTheory.GenExtend
theorem _root_.solution {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {φ' : I → (Y' ⟶ X)} {ε : I → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y')
    (h : ∀ i, r ≫ φ i = r' ≫ φ' i)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t r) (LB.pullGen L _ _ t' r')) (z : Z)
    (a : I → L.ι) (ha : r z ∈ LB.wchart L φ a) (ha' : r' z ∈ LB.wchart L φ' a) :
    gm r z (LB.wchart L φ a) (t.s a) = gm r' z (LB.wchart L φ' a) (t'.s a) := by
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have hv := val_corr hJ hc (𝟙 Z)
  rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at hv
  rw [gen_trans ht r z ha (Good.mem hJ φ r), gen_trans ht' r' z ha' (Good.mem hJ φ' r')]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) hv
  show gm (r ≫ φ k) z (L.U (a k) ⊓ L.U (J (r ≫ φ k))) (L.g (a k) (J (r ≫ φ k))) ^ _ =
    gm (r' ≫ φ' k) z (L.U (a k) ⊓ L.U (J (r' ≫ φ' k))) (L.g (a k) (J (r' ≫ φ' k))) ^ _
  rw [h k]
end GlobalTheory.GenExtend

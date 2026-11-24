-- Prove2me | solution 1 for GlobalTheory.GenExtend.res_pullU_eq_of_corr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:41:06.174804+00:00
-- url     : https://prove2.me/submissions/7876166b-ad1c-4a31-825f-4940a0a7e7da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
import Theorems.Thm_GlobalTheory_GenExtend_gm_eq_of_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t r) (LB.pullGen L _ _ t' r'))
    (a : I → L.ι) {A : Z.Opens} (hA : A ≤ r ⁻¹ᵁ LB.wchart L φ a)
    (hA' : A ≤ r' ⁻¹ᵁ LB.wchart L φ' a) :
    r'.appLE (LB.wchart L φ' a) A hA' (LB.ts t' a : Γ(Y', LB.wchart L φ' a)ˣ) =
      r.appLE (LB.wchart L φ a) A hA (LB.ts t a : Γ(Y, LB.wchart L φ a)ˣ) := by
  have hur : res hA' (pullU r' (LB.wchart L φ' a) (t'.s a)) =
      res hA (pullU r (LB.wchart L φ a) (t.s a)) := by
    refine unit_ext fun z hz => ?_
    rw [gm_res _ z hA hz, gm_res _ z hA' hz, gm_pull _ r z _ (hA hz), gm_pull _ r' z _ (hA' hz),
      Category.id_comp, Category.id_comp]
    exact (gm_eq_of_corr hL ht ht' r r' h hc z a (hA hz) (hA' hz)).symm
  exact congrArg Units.val hur
end GlobalTheory.GenExtend

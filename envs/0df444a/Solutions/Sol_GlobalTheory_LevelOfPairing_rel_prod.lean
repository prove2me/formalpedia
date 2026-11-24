-- Prove2me | solution 1 for GlobalTheory.LevelOfPairing.rel_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:32.226724+00:00
-- url     : https://prove2.me/submissions/edad7c0c-54f0-408e-b732-b90efc48ba58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsLevelStructureOfWeilPairing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.LevelOfPairing
variable {G U : Type} [Group G] [CommGroup U] {R : G → G → U → Prop} {M : ℕ}
namespace GlobalTheory.LevelOfPairing
theorem _root_.solution (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {y : G}
    (h₁ : R 1 y 1) : ∀ {n : ℕ} (x : Fin n → G) (c : Fin n → U), (∀ i, R (x i) y (c i)) →
      R (List.ofFn x).prod y (∏ i, c i)
  | 0, _, _, _ => by simpa using h₁
  | n + 1, x, c, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    exact hm _ _ _ _ _ (h 0) (solution hm h₁ _ _ fun i => h i.succ)
end GlobalTheory.LevelOfPairing

-- Prove2me | solution 1 for GlobalTheory.InvFieldRing.appLE_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:01:27.75417+00:00
-- url     : https://prove2.me/submissions/c932edb1-ffd5-4ca4-9857-8bdba0092528

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
noncomputable section
open GlobalTheory GlobalTheory.InvFieldRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.InvFieldRing
theorem _root_.solution {Y Z : Scheme.{0}} (g : Z ⟶ Y) {V V' : Y.Opens} {W W' : Z.Opens} (h : V' ≤ V) (h' : W' ≤ W)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W' ≤ g ⁻¹ᵁ V') (f : Γ(Y, V)) :
    (g.appLE V' W' e').hom (resG Y h f) = resG Z h' ((g.appLE V W e).hom f) := by
  change (Y.presheaf.map (homOfLE h).op ≫ g.appLE V' W' e').hom f = (g.appLE V W e ≫ Z.presheaf.map (homOfLE h').op).hom f
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
end GlobalTheory.InvFieldRing

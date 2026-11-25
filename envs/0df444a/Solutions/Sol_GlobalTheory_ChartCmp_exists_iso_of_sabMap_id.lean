-- Prove2me | solution 1 for GlobalTheory.ChartCmp.exists_iso_of_sabMap_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:39:20.884017+00:00
-- url     : https://prove2.me/submissions/b91cb286-d31e-416c-bb6b-240066f51fa8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapId
import Theorems.Thm_GlobalTheory_ChartCmp_isMonHom_of_mul_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubeMap_comp_proj_three
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_hom_ext_triple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mul_left_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), ∃ ψ : t.G ≅ t'.G, ψ.hom.left = n.φ ∧ IsMonHom ψ.hom ∧ (∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a) ∧ n.cm.F3 = (ψ.hom ⊗ₘ ψ.hom ⊗ₘ ψ.hom).left ∧ ∃ w : LB.Iso t.PP.L (t'.PP.L.pull n.φ), CubIso n w := by
  intro E _ _ _ H V _ t t' n
  have hp := n.cart.1
  have hw : n.cm.F ≫ t'.G.hom = t.G.hom := by simpa using hp.w
  haveI : IsIso n.cm.F := hp.isIso_fst_of_isIso
  let ψ : t.G ≅ t'.G := Over.isoMk (asIso n.cm.F) hw
  have hψ : ψ.hom.left = n.cm.F := rfl
  refine ⟨ψ, rfl, ?_, fun a => ?_, ?_, ?_⟩
  · refine isMonHom_of_mul_points _ fun T x y => ?_
    apply Over.OverMorphism.ext
    have e := n.cart.2 T x y (pushPt hp.w x) (pushPt hp.w y) rfl rfl
    rw [Over.comp_left, hψ, ← e]
    exact mul_left_congr (Category.comp_id _) _ _ (x ≫ ψ.hom) (y ≫ ψ.hom) rfl rfl
  · apply Over.OverMorphism.ext
    exact n.act a
  · refine hom_ext_triple _ fun i => ?_
    rw [cubeMap_comp_proj_three, ← Over.comp_left, ← cubeProj_comp_map, Over.comp_left, hψ]
  · obtain ⟨w, h1, -, h3⟩ := n.lin
    exact ⟨w, h1, h3⟩
end GlobalTheory.ChartCmp

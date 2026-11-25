-- Prove2me | solution 1 for GlobalTheory.PushChart.isCombAtG_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:12.468054+00:00
-- url     : https://prove2.me/submissions/3cb6bb37-89d7-40ec-86e0-0669131a3f1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PushChart
import Theorems.Thm_GlobalTheory_PushChart_prod_ofFn_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.PushChart
namespace GlobalTheory.PushChart
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t t' : SAB H X0}
    (ψ : t.G ⟶ t'.G) [IsMonHom ψ] {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {v' : Fin m → (Sp (DualNumber S) ⟶ t'.G.left)}
    (hv : ∀ i, v' i = v i ≫ ψ.left) {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x0 v cf w) : IsCombAtG t' x0 v' cf (w ≫ ψ.left) := by
  obtain ⟨u, hu, hw⟩ := h
  refine ⟨fun i => u i ≫ ψ, fun i => ?_, ?_⟩
  · rw [hv, Over.comp_left, hu]
    exact Category.assoc _ _ _
  · rw [← prod_ofFn_comp, Over.comp_left, hw]
end GlobalTheory.PushChart

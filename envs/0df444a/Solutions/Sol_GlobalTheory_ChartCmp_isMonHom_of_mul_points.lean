-- Prove2me | solution 1 for GlobalTheory.ChartCmp.isMonHom_of_mul_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:51:10.656969+00:00
-- url     : https://prove2.me/submissions/45e57037-2b41-4b85-882f-4b60b451e099

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapId

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
theorem _root_.solution {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G')
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f where
  one_hom := by
    have e := h (𝟙_ _) 1 1
    rw [_root_.mul_one] at e
    have e2 : (1 : 𝟙_ (Over S) ⟶ G) ≫ f = 1 := by
      have := e.symm
      exact mul_eq_left.1 this
    simpa [Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _)] using e2
  mul_hom := by
    have e := h _ (fst G G) (snd G G)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at e
    rw [e, ← lift_fst_comp_snd_comp]
end GlobalTheory.ChartCmp

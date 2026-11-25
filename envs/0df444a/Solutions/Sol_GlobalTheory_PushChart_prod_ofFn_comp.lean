-- Prove2me | solution 1 for GlobalTheory.PushChart.prod_ofFn_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:47:52.671312+00:00
-- url     : https://prove2.me/submissions/d83dfa45-207b-4cbb-b491-ca477f2ebc09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PushChart
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.PushChart
namespace GlobalTheory.PushChart
theorem _root_.solution {S : Scheme.{0}} {T G G' : Over S} [GrpObj G] [GrpObj G'] (ψ : G ⟶ G') [IsMonHom ψ]
    {m : ℕ} (u : Fin m → (T ⟶ G)) : (List.ofFn u).prod ≫ ψ = (List.ofFn fun i => u i ≫ ψ).prod := by
  induction m with
  | zero => simp [MonObj.one_comp]
  | succ m ih => rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.mul_comp, ih]
end GlobalTheory.PushChart

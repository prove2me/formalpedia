-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CoordDir.comb_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:40.143465+00:00
-- url     : https://prove2.me/submissions/02824682-d0c5-4738-a475-ba46a31f4457

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TangentDirectionTwoChartsLinearPart
import Theorems.Thm_GlobalTheory_ChartCmp_CoordDir_tanPt_sum
import Theorems.Thm_GlobalTheory_ChartCmp_CoordDir_eps_tanPt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_jetTan_eq_tp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_fin_one_pair_eq


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.CoordDir
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
  {t : SAB H (Sp V)} {d : ℕ}
variable {κ : Type} [Fintype κ] {G : FGLaw V d} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V}
  {tg : κ → (Sp (DualNumber V) ⟶ t.G.left)} {uv : κ → Fin d → V} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G}
namespace GlobalTheory.ChartCmp.CoordDir
theorem _root_.solution (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) {u : Fin d → V} {v : Sp (DualNumber V) ⟶ t.G.left}
    (h : IsCombAtG t (𝟙 (Sp V)) (dirs x) u v) : (tanPt x fun q => u q.2).left = v := by
  obtain ⟨w, hw, hprod⟩ := h
  have hw' : w = fun i => tanPt x (u i • fun q : Fin 1 × Fin d => if q = ((0 : Fin 1), i) then (1 : V) else 0) := by
    funext i
    apply Over.OverMorphism.ext
    rw [hw i, dirs, jetTan_eq_tp, eps_tanPt]
  have hq : ∀ (q : Fin 1 × Fin d) (i : Fin d), (q = ((0 : Fin 1), i)) = (i = q.2) := fun q i =>
    propext ⟨fun h => by rw [h], fun h => by rw [h, fin_one_pair_eq]⟩
  have hs : (∑ i, u i • fun q : Fin 1 × Fin d => if q = ((0 : Fin 1), i) then (1 : V) else 0) =
      fun q => u q.2 := by
    funext q
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hq, mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  rw [← hs, tanPt_sum hx, ← hprod, hw']
end GlobalTheory.ChartCmp.CoordDir

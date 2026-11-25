-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CoordDir.tanPt_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:44.08299+00:00
-- url     : https://prove2.me/submissions/8ba28bba-0be0-4d0c-9919-df23b5a954ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TangentDirectionTwoChartsLinearPart
import Theorems.Thm_GlobalTheory_ChartCmp_CoordDir_fst_tp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp


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
theorem _root_.solution {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} (hx : GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x)
    {g g' : Fin 1 × Fin d → V} (h : tanPt x g = tanPt x g') : g = g' := by
  have hz : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) ≫ x 1 = 1 := hx.2.1 1
  have h0 : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (TrivSqZeroExt.fstHom V V V) ≫ tanPt x g = 1 := by
    rw [tanPt, ← Category.assoc, GermD.homAt_comp, fst_tp, hz]
  have e : tp g = tp g' :=
    (hx.2.2 (DualNumber V) (TrivSqZeroExt.fstHom V V V) (0 + 1) ker_fst_sq (tanPt x g) h0).unique
      ⟨fst_tp g, rfl⟩ ⟨fst_tp g', h⟩
  funext q
  have := congrArg (fun ψ : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V =>
    ψ (Ideal.Quotient.mk _ (MvPolynomial.X q))) e
  simp only [tp_mk] at this
  exact TrivSqZeroExt.inr_injective this
end GlobalTheory.ChartCmp.CoordDir

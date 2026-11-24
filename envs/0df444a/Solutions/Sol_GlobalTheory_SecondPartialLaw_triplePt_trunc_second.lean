-- Prove2me | solution 1 for GlobalTheory.SecondPartialLaw.triplePt_trunc_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:54:55.450994+00:00
-- url     : https://prove2.me/submissions/76d0f020-113f-4d2b-b770-98251fb49992

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Theorems.Thm_GlobalTheory_SecondPartialLaw_jpt_trunc_ring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
noncomputable section
open GlobalTheory GlobalTheory.SecondPartialLaw
namespace GlobalTheory.SecondPartialLaw
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
    {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
    {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
    (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) (i j k : Fin 3) :
    (ρn x0 d 3 m).left ≫ (lift (jptG t x0 d x (m + 1) i) (lift (jptG t x0 d x (m + 1) j) (jptG t x0 d x (m + 1) k))).left =
      𝟙 _ ≫ (lift (jptG t x0 d x m i) (lift (jptG t x0 d x m j) (jptG t x0 d x m k))).left := by
  rw [← Over.comp_left, Category.id_comp, comp_lift, comp_lift, jpt_trunc_ring hch, jpt_trunc_ring hch, jpt_trunc_ring hch]
end GlobalTheory.SecondPartialLaw

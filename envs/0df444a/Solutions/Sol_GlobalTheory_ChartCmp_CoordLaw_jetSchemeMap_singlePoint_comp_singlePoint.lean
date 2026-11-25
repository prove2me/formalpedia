-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CoordLaw.jetSchemeMap_singlePoint_comp_singlePoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:41:29.864009+00:00
-- url     : https://prove2.me/submissions/39c18cb2-6508-4d7e-bb1c-3b1e888ffa33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRel
import Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_ev_one_eq
import Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_hom_comp

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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.CoordLaw
open Formalism.MainNotions.ModuliIntegralCharts.H1
variable {V : Type} [CommRing V] {d : ℕ}
namespace GlobalTheory.ChartCmp.CoordLaw
theorem _root_.solution (m : ℕ) {n : ℕ} (a : Pt V n d) (φ : Pt V 1 d)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    sub1 m a ≫ sub1 m φ = sub1 m (comp1 φ a) := by
  have e : sub1 m (comp1 φ a) = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin 1 × Fin d =>
      MvPowerSeries.subst (fun q : Fin 1 × Fin d => a q.2) (φ p.2)) := by
    simp only [sub1, comp1, ev_one_eq]
  rw [e]
  exact hom_comp m _ _ (fun p => hφ p.2) (fun p => ha p.2)
end GlobalTheory.ChartCmp.CoordLaw

-- Prove2me | solution 1 for GlobalTheory.ChartCmp.exists_coordRel_of_isUnivJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:52:25.130883+00:00
-- url     : https://prove2.me/submissions/a9c24479-395e-45b5-bd96-777a8acbea7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsCoordinateRelationUniversalJets
import Theorems.Thm_GlobalTheory_ChartCmp_Coord_jetSubstP_trunc
import Theorems.Thm_GlobalTheory_ChartCmp_Coord_exists_coord
import Theorems.Thm_GlobalTheory_ChartCmp_Coord_subst_eq_X

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
open GlobalTheory GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp
theorem _root_.solution : ∀ (V : Type) [CommRing V] (G : Over (Sp V)) [GrpObj G] (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x' → ∃ φ φi : Pt V 1 d, IsInvPair φ φi ∧ CoordRel x x' φ ∧ CoordRel x' x φi := by
  intro V _ G _ d x x' hx hx'
  obtain ⟨φ, h0, hφ⟩ := Coord.exists_coord hx hx'
  obtain ⟨φi, h0i, hφi⟩ := Coord.exists_coord hx' hx
  have key : ∀ f : Fin 1 × Fin d → MvPowerSeries (Fin 1 × Fin d) V, (fun p : Fin 1 × Fin d => f (0, p.2)) = f := by
    intro f
    funext p
    rw [show ((0 : Fin 1), p.2) = p from Prod.ext (Subsingleton.elim _ _) rfl]
  have key2 : ∀ f : Fin 1 × Fin d → MvPowerSeries (Fin 1 × Fin d) V,
      (fun p : Fin 1 × Fin d => (![fun j => f (0, j)] : Fin 1 → Pt V 1 d) p.1 p.2) = f := by
    intro f
    funext p
    obtain ⟨a, b⟩ := p
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  refine ⟨fun j => φ (0, j), fun j => φi (0, j), ⟨fun i => h0 _, fun i => h0i _, ?_, ?_⟩, fun m => ?_, fun m => ?_⟩
  · funext i
    simp only [comp1, ev, pt]
    rw [key2]
    exact Coord.subst_eq_X hx h0 hφ h0i hφi _
  · funext i
    simp only [comp1, ev, pt]
    rw [key2]
    exact Coord.subst_eq_X hx' h0i hφi h0 hφ _
  · rw [Coord.jetSubstP_trunc m (fun p : Fin 1 × Fin d => φ (0, p.2)), key]
    exact hφ m
  · rw [Coord.jetSubstP_trunc m (fun p : Fin 1 × Fin d => φi (0, p.2)), key]
    exact hφi m
end GlobalTheory.ChartCmp

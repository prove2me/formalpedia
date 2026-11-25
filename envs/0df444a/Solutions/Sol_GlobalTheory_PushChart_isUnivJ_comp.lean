-- Prove2me | solution 1 for GlobalTheory.PushChart.isUnivJ_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:14:07.191471+00:00
-- url     : https://prove2.me/submissions/bd8f64fa-7edf-409c-ac1a-4f91c870bd8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PushChart

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
theorem _root_.solution {V : Type} [CommRing V] {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] (ψ : G ≅ G') [IsMonHom ψ.hom]
    {κ : Type} {z : GlobalTheory.PowGerm.JetPts G κ} (h : GlobalTheory.PowGerm.IsUnivJ G κ z) :
    GlobalTheory.PowGerm.IsUnivJ G' κ (fun m => z m ≫ ψ.hom) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun m => ?_, fun m => ?_, ?_⟩
  · rw [← Category.assoc, h1]
  · rw [← Category.assoc, h2, MonObj.one_comp]
  · intro A _ _ aug m hm y hy
    have hy' : Formalism.L2.Pj.homAt (𝟙 (Sp V)) aug ≫ (y ≫ ψ.inv) = 1 := by
      rw [← cancel_mono ψ.hom, MonObj.one_comp]
      simpa using hy
    obtain ⟨f, ⟨hf1, hf2⟩, hf3⟩ := h3 A aug m hm (y ≫ ψ.inv) hy'
    refine ⟨f, ⟨hf1, ?_⟩, fun g hg => hf3 g ⟨hg.1, ?_⟩⟩
    · rw [← Category.assoc, ← hf2]; simp
    · rw [hg.2]; simp
end GlobalTheory.PushChart

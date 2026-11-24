-- Prove2me | solution 1 for GlobalTheory.JetSer.exists_index_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:28.881005+00:00
-- url     : https://prove2.me/submissions/1d7ef8e3-be5f-46a9-a243-b4c6ac64178c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIndexOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
namespace GlobalTheory.JetSer
theorem _root_.solution {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (e : Spec (CommRingCat.of R) ⟶ X) : ∃ j : L.ι, ⊤ ≤ e ⁻¹ᵁ L.U j := by
  have h : e (IsLocalRing.closedPoint R) ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨j, (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of R) e hj).ge⟩
end GlobalTheory.JetSer

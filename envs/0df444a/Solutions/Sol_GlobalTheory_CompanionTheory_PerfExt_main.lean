-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfExt.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:03:20.975809+00:00
-- url     : https://prove2.me/submissions/bae5926b-0d05-4875-8949-b80920d1e0ed

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_perf_ext

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfExt
namespace GlobalTheory.CompanionTheory.PerfExt
theorem _root_.solution : PerfBaseSt := by
  intro R _ P _ _ F h R' _ _ F' m
  haveI : Finite Pᵒᵖ := Finite.of_injective unop unop_injective
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun _ _ ↦ Finite.of_subsingleton
  exact perf_ext m h
end GlobalTheory.CompanionTheory.PerfExt

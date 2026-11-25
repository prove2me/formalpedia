-- Prove2me | solution 1 for GlobalTheory.IntSeries.intAA_iff_exists_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:55:56.971864+00:00
-- url     : https://prove2.me/submissions/40a7b018-182a-4d29-a80b-a54898471857

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Theorems.Thm_GlobalTheory_IntSeries_intAA_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.IntSeries
variable {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] {σ τ : Type}
namespace GlobalTheory.IntSeries
theorem _root_.solution {f : MvPowerSeries σ k} :
    IntAA (R := R) k f ↔ ∃ g : MvPowerSeries σ R, MvPowerSeries.map (algebraMap R k) g = f := by
  refine ⟨fun h => ?_, fun ⟨g, hg⟩ => hg ▸ intAA_map g⟩
  choose g hg using h
  exact ⟨g, MvPowerSeries.ext fun n => (coeff_map _ _ _).trans (hg n)⟩
end GlobalTheory.IntSeries

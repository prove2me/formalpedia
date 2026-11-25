-- Prove2me | solution 1 for GlobalTheory.IntSeries.intAA_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:47.71034+00:00
-- url     : https://prove2.me/submissions/5765018e-e6ba-4e91-b4ff-1651680465a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst

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
theorem _root_.solution {ι : Type*} (t : Finset ι) {f : ι → MvPowerSeries σ k}
    (hf : ∀ i ∈ t, IntAA (R := R) k (f i)) : IntAA (R := R) k (∑ i ∈ t, f i) := fun n => by
  rw [map_sum]; exact Subring.sum_mem _ fun i hi => hf i hi n
end GlobalTheory.IntSeries

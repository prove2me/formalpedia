-- Prove2me | solution 1 for GlobalTheory.IntSeries.intAA_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:46.009588+00:00
-- url     : https://prove2.me/submissions/5beaed0b-2c8c-4d9a-a9f1-43106d6ce82c

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
theorem _root_.solution : IntAA (R := R) k (1 : MvPowerSeries σ k) := by
  simpa using intAA_map (k := k) (1 : MvPowerSeries σ R)
end GlobalTheory.IntSeries

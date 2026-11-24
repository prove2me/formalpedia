-- Prove2me | solution 1 for GlobalTheory.IntSeries.intAA_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:47:39.975913+00:00
-- url     : https://prove2.me/submissions/fde936b2-dfac-4062-8a17-7ad4039c28b6

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
theorem _root_.solution {f g : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (hg : IntAA (R := R) k g) :
    IntAA (R := R) k (f + g) := fun n => by
  rw [map_add]; exact Subring.add_mem _ (hf n) (hg n)
end GlobalTheory.IntSeries

-- Prove2me | solution 1 for GlobalTheory.IntSeries.intAA_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:58:22.589871+00:00
-- url     : https://prove2.me/submissions/8907b626-5fd3-4885-9a67-4e7fefa7602e

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
theorem _root_.solution (r : R) {f : MvPowerSeries σ k} (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (algebraMap R k r • f) := fun n => by
  rw [map_smul, smul_eq_mul]; exact Subring.mul_mem _ ⟨r, rfl⟩ (hf n)
end GlobalTheory.IntSeries

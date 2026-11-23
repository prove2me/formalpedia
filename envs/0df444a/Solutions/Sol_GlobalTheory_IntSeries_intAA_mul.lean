-- Prove2me | solution 1 for GlobalTheory.IntSeries.intAA_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:56.222618+00:00
-- url     : https://prove2.me/submissions/013ca2ec-a7c9-4e01-94c6-fae913eb2c85

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
    IntAA (R := R) k (f * g) := fun n => by
  classical
  rw [coeff_mul]
  exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (hf _) (hg _)
end GlobalTheory.IntSeries

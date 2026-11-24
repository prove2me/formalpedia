-- Prove2me | solution 1 for GlobalTheory.IntSeries.intAA_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:47:42.338195+00:00
-- url     : https://prove2.me/submissions/a79eca27-5048-4989-b7aa-d0a8f0c53243

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
theorem _root_.solution {f : MvPowerSeries σ k} (s : σ) (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (pderiv k s f) := fun n => by
  rw [coeff_pderiv]
  exact Subring.mul_mem _ (hf _) (Subring.add_mem _ (natCast_mem _ _) (Subring.one_mem _))
end GlobalTheory.IntSeries

-- Prove2me | solution 1 for GlobalTheory.IntSeries.intAA_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:47:47.69718+00:00
-- url     : https://prove2.me/submissions/547d8367-8c5d-4a22-be7d-3e2e3c3403fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Theorems.Thm_GlobalTheory_IntSeries_intAA_one
import Theorems.Thm_GlobalTheory_IntSeries_intAA_mul

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
    (hf : ∀ i ∈ t, IntAA (R := R) k (f i)) : IntAA (R := R) k (∏ i ∈ t, f i) :=
  Finset.prod_induction f (IntAA (R := R) k) (fun _ _ => intAA_mul) intAA_one hf
end GlobalTheory.IntSeries

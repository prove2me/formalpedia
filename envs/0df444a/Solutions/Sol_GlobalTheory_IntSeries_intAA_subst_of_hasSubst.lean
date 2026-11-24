-- Prove2me | solution 1 for GlobalTheory.IntSeries.intAA_subst_of_hasSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:07:14.782253+00:00
-- url     : https://prove2.me/submissions/6714f99f-c438-4abd-bf27-49d8d3dbfde4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Theorems.Thm_GlobalTheory_IntSeries_intAA_pow
import Theorems.Thm_GlobalTheory_IntSeries_intAA_prod

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
theorem _root_.solution {a : σ → MvPowerSeries τ k} (ha : HasSubst a)
    {f : MvPowerSeries σ k} (hai : ∀ s, IntAA (R := R) k (a s)) (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (MvPowerSeries.subst a f) := fun n => by
  rw [coeff_subst ha]
  refine finsum_induction (· ∈ (algebraMap R k).range) (Subring.zero_mem _)
    (fun _ _ => Subring.add_mem _) fun d => ?_
  rw [smul_eq_mul]
  exact Subring.mul_mem _ (hf d) (intAA_prod _ (fun s _ => intAA_pow (hai s) _) n)
end GlobalTheory.IntSeries

-- Prove2me | solution 1 for GlobalTheory.IntSeries.intAA_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:47:45.798555+00:00
-- url     : https://prove2.me/submissions/7c7151b3-7d46-4032-9db8-49b185331402

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
theorem _root_.solution {f : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (m : ℕ) :
    IntAA (R := R) k (f ^ m) := by
  induction m with
  | zero => simpa using intAA_one
  | succ m ih => rw [pow_succ]; exact intAA_mul ih hf
end GlobalTheory.IntSeries

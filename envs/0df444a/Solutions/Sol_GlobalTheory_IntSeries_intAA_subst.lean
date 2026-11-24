-- Prove2me | solution 1 for GlobalTheory.IntSeries.intAA_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:26:54.798+00:00
-- url     : https://prove2.me/submissions/56f99665-9a83-416e-8e98-66e07ce2de68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Theorems.Thm_GlobalTheory_IntSeries_intAA_subst_of_hasSubst

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
theorem _root_.solution [Finite σ] {a : σ → MvPowerSeries τ k} {f : MvPowerSeries σ k}
    (ha : ∀ s, constantCoeff (a s) = 0) (hai : ∀ s, IntAA (R := R) k (a s))
    (hf : IntAA (R := R) k f) : IntAA (R := R) k (MvPowerSeries.subst a f) :=
  intAA_subst_of_hasSubst (hasSubst_of_constantCoeff_zero ha) hai hf
end GlobalTheory.IntSeries

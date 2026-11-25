-- Prove2me | solution 1 for GlobalTheory.FramePull.expIntegral_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:59:50.218816+00:00
-- url     : https://prove2.me/submissions/b12bdf83-0f40-4449-9c17-2dde96109963

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_GlobalTheory_FramePull_ExpIntegral_add
import Theorems.Thm_GlobalTheory_FramePull_ExpIntegral_neg
import Theorems.Thm_GlobalTheory_FramePull_powerSeriesExpIntegral_canonGauge_additive_second

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FramePull
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O)
variable {B} {h : PS k 2 d}
namespace GlobalTheory.FramePull
theorem _root_.solution (hh : B.IsCanonGauge k h) (b c : O) (j : ℕ) :
    ExpIntegral R ((j : k) • ev ![B.actK k b, B.actK k c] h - ev ![B.actK k b, B.actK k ((j : O) * c)] h) := by
  induction j with
  | zero =>
    have := (powerSeriesExpIntegral_canonGauge_additive_second hh b 0 0).neg
    simpa using this
  | succ j ih =>
    have := ih.add (powerSeriesExpIntegral_canonGauge_additive_second hh b ((j : O) * c) c)
    convert this using 1
    rw [Nat.cast_succ, Nat.cast_succ, add_smul, one_smul, add_mul, _root_.one_mul]
    ring
end GlobalTheory.FramePull

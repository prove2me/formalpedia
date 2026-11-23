-- Prove2me | solution 1 for GlobalTheory.FormalSeries.coeff_eq_of_le_order_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:50.517803+00:00
-- url     : https://prove2.me/submissions/1983f560-17a4-4c62-8513-83046be1c4b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]
namespace GlobalTheory.FormalSeries
theorem _root_.solution {k : ℕ} {f g : MvPowerSeries σ R} (h : (k : ℕ∞) ≤ (f - g).order)
    {d : σ →₀ ℕ} (hd : d.degree < k) : coeff d f = coeff d g := by
  have h' : (d.degree : ℕ∞) < (f - g).order := lt_of_lt_of_le (by exact_mod_cast hd) h
  have := coeff_of_lt_order h'
  rwa [map_sub, sub_eq_zero] at this
end GlobalTheory.FormalSeries

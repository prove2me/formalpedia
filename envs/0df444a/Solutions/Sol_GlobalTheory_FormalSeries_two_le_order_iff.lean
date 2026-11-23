-- Prove2me | solution 1 for GlobalTheory.FormalSeries.two_le_order_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:21.179631+00:00
-- url     : https://prove2.me/submissions/8de5bc7f-4a82-435e-8e91-3435b9909663

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Theorems.Thm_GlobalTheory_FormalSeries_eq_zero_or_single_of_degree_lt_two

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
theorem _root_.solution {f : MvPowerSeries σ R} :
    2 ≤ f.order ↔ constantCoeff f = 0 ∧ ∀ j, coeff (Finsupp.single j 1) f = 0 := by
  constructor
  · intro h
    refine ⟨?_, fun j => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply]
      refine coeff_of_lt_order ?_
      rw [map_zero, Nat.cast_zero]
      exact lt_of_lt_of_le (by norm_num) h
    · refine coeff_of_lt_order ?_
      rw [Finsupp.degree_single, Nat.cast_one]
      exact lt_of_lt_of_le (by norm_num) h
  · rintro ⟨h0, h1⟩
    have : ((2 : ℕ) : ℕ∞) ≤ f.order := nat_le_order fun d hd => by
      rcases eq_zero_or_single_of_degree_lt_two hd with rfl | ⟨j, rfl⟩
      · rw [coeff_zero_eq_constantCoeff_apply]
        exact h0
      · exact h1 j
    exact_mod_cast this
end GlobalTheory.FormalSeries

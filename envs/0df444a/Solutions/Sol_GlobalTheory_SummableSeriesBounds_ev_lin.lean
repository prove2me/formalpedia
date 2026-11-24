-- Prove2me | solution 1 for GlobalTheory.SummableSeriesBounds.ev_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:58:48.657623+00:00
-- url     : https://prove2.me/submissions/f7de8ec9-9bad-4f91-a49e-9fbb08e54f5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableSeriesBounds
open PowerSeries Filter Topology
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
namespace GlobalTheory.SummableSeriesBounds
theorem _root_.solution [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) : ev hπ (lin π) = 0 := by
  change ∑' n, coeff n (X - PowerSeries.C π : PowerSeries C) * π ^ n = 0
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, coeff_C, coeff_X]
  · intro n hn
    have h0 : n ≠ 0 := by rintro rfl; simp at hn
    have h1 : n ≠ 1 := by rintro rfl; simp at hn
    simp [coeff_C, coeff_X, h0, h1]
end GlobalTheory.SummableSeriesBounds

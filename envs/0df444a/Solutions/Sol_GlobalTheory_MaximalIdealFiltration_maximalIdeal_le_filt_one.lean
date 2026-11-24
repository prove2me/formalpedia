-- Prove2me | solution 1 for GlobalTheory.MaximalIdealFiltration.maximalIdeal_le_filt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:54:28.802986+00:00
-- url     : https://prove2.me/submissions/3993e9e7-5bcd-4ff6-82d7-45f2340d5f3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MaximalIdealLeFiltOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaximalIdealFiltration
open MvPowerSeries
variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
namespace GlobalTheory.MaximalIdealFiltration
theorem _root_.solution :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ≤ filt (O := O) 1 := by
  intro f hf m
  by_cases h0 : m = 0
  · subst h0
    simp only [map_zero, Nat.sub_zero, pow_one]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hf ⊢
    intro hu
    apply hf
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hu
  · have : 1 ≤ m.degree := by
      rw [Nat.one_le_iff_ne_zero]
      intro h
      exact h0 ((Finsupp.degree_eq_zero_iff m).1 h)
    have : 1 - m.degree = 0 := by omega
    rw [this, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
end GlobalTheory.MaximalIdealFiltration

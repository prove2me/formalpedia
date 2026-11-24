-- Prove2me | solution 1 for GlobalTheory.FiltrationMultiplicative.max_le_filt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:04:33.667869+00:00
-- url     : https://prove2.me/submissions/44de3ac7-d6ad-4687-b49b-33a183271f06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow
import Theorems.Thm_GlobalTheory_FiltrationMultiplicative_mem_max_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open GlobalTheory GlobalTheory.FiltrationMultiplicative
variable {O : Type} [CommRing O] [IsLocalRing O]
namespace GlobalTheory.FiltrationMultiplicative
theorem _root_.solution {σ : Type} :
    IsLocalRing.maximalIdeal (MvPowerSeries σ O) ≤ FiltIdeal O σ 1 := by
  intro f hf m
  by_cases h : Finsupp.degree m = 0
  · have hm : m = 0 := (Finsupp.degree_eq_zero_iff m).mp h
    subst hm
    simpa using (mem_max_iff f).mp hf
  · have : 1 - Finsupp.degree m = 0 := by omega
    rw [this, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
end GlobalTheory.FiltrationMultiplicative

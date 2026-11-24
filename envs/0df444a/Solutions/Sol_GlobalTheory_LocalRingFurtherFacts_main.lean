-- Prove2me | solution 1 for GlobalTheory.LocalRingFurtherFacts.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:48:56.300874+00:00
-- url     : https://prove2.me/submissions/55663810-ed8a-4f3d-9f91-728331958010

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LocalRingFurtherFacts
namespace GlobalTheory.LocalRingFurtherFacts
theorem _root_.solution {O : Type} [CommRing O] [IsLocalRing O] {a k : ℕ} {c : O}
    (hc : c ∈ IsLocalRing.maximalIdeal O ^ k) :
    (MvPowerSeries.C : O → MvPowerSeries (Fin a) O) c ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ k := by
  have h1 : Ideal.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin a) O) (IsLocalRing.maximalIdeal O)
      ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (IsLocalRing.mem_maximalIdeal x).mp hx
    have := hu.map (MvPowerSeries.constantCoeff : MvPowerSeries (Fin a) O →+* O)
    simpa using this
  have h2 := Ideal.mem_map_of_mem (MvPowerSeries.C : O →+* MvPowerSeries (Fin a) O) hc
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 k h2
end GlobalTheory.LocalRingFurtherFacts

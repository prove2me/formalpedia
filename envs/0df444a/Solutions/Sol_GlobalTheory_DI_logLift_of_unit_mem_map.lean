-- Prove2me | solution 1 for GlobalTheory.DI.logLift_of_unit_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:41:49.07443+00:00
-- url     : https://prove2.me/submissions/da6ad9c9-f771-42dd-a06d-7c6141dc212f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogLiftOfUnitMemMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option autoImplicit false
namespace GlobalTheory.DI
namespace _root_.GlobalTheory.DI
theorem _root_.solution : ∀ {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (s : Finset ι) (At : Subring Kt), _root_.GlobalTheory.DI.IsFlatLift p π →
    (∀ i ∈ s, ∀ z ∈ At, ∃ w ∈ At, F i z = z ^ p + p * w) → ∀ g : K, g ≠ 0 → g ∈ At.map π →
    g⁻¹ ∈ At.map π → _root_.GlobalTheory.DI.LogLift p π F s (At.map π : Set K) g := by
  intro K Kt _ _ p _ _ π ι F s At hflat hF g hg hmem hinv
  obtain ⟨z, hz, rfl⟩ := Subring.mem_map.mp hmem
  obtain ⟨y, hy, hyz⟩ := Subring.mem_map.mp hinv
  unfold _root_.GlobalTheory.DI.LogLift
  refine ⟨z, rfl, fun i hi => ?_⟩
  obtain ⟨w, hw, hFw⟩ := hF i hi z hz
  refine ⟨y ^ p * w, Subring.mem_map.mpr ⟨y ^ p * w, At.mul_mem (At.pow_mem hy p) hw, rfl⟩, ?_⟩
  have h0 : (p : Kt) * (w - z ^ p * y ^ p * w) = 0 := by
    rw [hflat.ann]
    simp only [map_sub, map_mul, map_pow, hyz]
    rw [← mul_pow, mul_inv_cancel₀ hg, one_pow, one_mul, sub_self]
  rw [hFw]
  linear_combination h0
end _root_.GlobalTheory.DI
end GlobalTheory.DI

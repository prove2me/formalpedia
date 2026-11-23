-- Prove2me | solution 1 for GlobalTheory.Phase.Ph.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:16.45111+00:00
-- url     : https://prove2.me/submissions/37208d78-9658-4143-8e2d-d1cb3810f710

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex
open GlobalTheory.SW
open GlobalTheory GlobalTheory.Phase
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
variable {n g : ℕ}
namespace GlobalTheory.Phase
namespace Ph
theorem _root_.solution {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, h⟩ := ha
  obtain ⟨k, hk, h'⟩ := hb
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  calc (a * b) ^ (m * k) = (a ^ m) ^ k * (b ^ k) ^ m := by ring
    _ = (((‖a * b‖ : ℝ) : ℂ)) ^ (m * k) := by
      rw [h, h', norm_mul, Complex.ofReal_mul]
      ring
end Ph
end GlobalTheory.Phase

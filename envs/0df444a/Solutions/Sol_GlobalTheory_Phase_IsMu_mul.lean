-- Prove2me | solution 1 for GlobalTheory.Phase.IsMu.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:58.911661+00:00
-- url     : https://prove2.me/submissions/e08881a6-32d1-4d46-90ee-eedbb825ed6d

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
namespace IsMu
theorem _root_.solution {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, h⟩ := ha
  obtain ⟨k, hk, h'⟩ := hb
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  calc (a * b) ^ (m * k) = (a ^ m) ^ k * (b ^ k) ^ m := by ring
    _ = 1 := by rw [h, h', one_pow, one_pow, one_mul]
end IsMu
end GlobalTheory.Phase
